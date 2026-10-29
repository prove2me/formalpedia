-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:12.526322+00:00
-- url     : https://prove2.me/submissions/2dc601df-32fb-4e4c-9ac2-8a17b9a2d1b8

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
theorem support_rectangle_w1384_s0_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784575239/10000000000 : ℝ)*x 0 + (1195794763/2000000000 : ℝ)*x 1 + (1205207621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784575239/10000000000 : ℝ)^543 ≤ (10487765425039/100000000000000 : ℝ)^415 := by
    have hnat : (1784575239 : ℕ)^543*100000000000000^415 ≤ 10487765425039^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784575239 10000000000 10487765425039 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195794763/2000000000 : ℝ)^543 ≤ (51018862940039/100000000000000 : ℝ)^415 := by
    have hnat : (1195794763 : ℕ)^543*100000000000000^415 ≤ 51018862940039^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195794763 2000000000 51018862940039 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205207621/2500000000 : ℝ)^543 ≤ (38493371622647/100000000000000 : ℝ)^415 := by
    have hnat : (1205207621 : ℕ)^543*100000000000000^415 ≤ 38493371622647^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205207621 2500000000 38493371622647 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784575239/10000000000 : ℝ), (1195794763/2000000000 : ℝ), (1205207621/2500000000 : ℝ)] ![(10487765425039/100000000000000 : ℝ), (51018862940039/100000000000000 : ℝ), (38493371622647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784575239/10000000000 : ℝ)|^543 ≤ (10487765425039/100000000000000 : ℝ)^415
        have hw : |(-1784575239/10000000000 : ℝ)|=(1784575239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195794763/2000000000 : ℝ)|^543 ≤ (51018862940039/100000000000000 : ℝ)^415
        have hw : |(1195794763/2000000000 : ℝ)|=(1195794763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205207621/2500000000 : ℝ)|^543 ≤ (38493371622647/100000000000000 : ℝ)^415
        have hw : |(1205207621/2500000000 : ℝ)|=(1205207621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1374278903/2500000000 : ℝ)*x 0 + (-610218651/2500000000 : ℝ)*x 1 + (1205207797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374278903/2500000000 : ℝ)^543 ≤ (22853551644377/50000000000000 : ℝ)^415 := by
    have hnat : (1374278903 : ℕ)^543*50000000000000^415 ≤ 22853551644377^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374278903 2500000000 22853551644377 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610218651/2500000000 : ℝ)^543 ≤ (15799517718191/100000000000000 : ℝ)^415 := by
    have hnat : (610218651 : ℕ)^543*100000000000000^415 ≤ 15799517718191^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610218651 2500000000 15799517718191 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205207797/2500000000 : ℝ)^543 ≤ (19246689488873/50000000000000 : ℝ)^415 := by
    have hnat : (1205207797 : ℕ)^543*50000000000000^415 ≤ 19246689488873^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205207797 2500000000 19246689488873 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374278903/2500000000 : ℝ), (-610218651/2500000000 : ℝ), (1205207797/2500000000 : ℝ)] ![(22853551644377/50000000000000 : ℝ), (15799517718191/100000000000000 : ℝ), (19246689488873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374278903/2500000000 : ℝ)|^543 ≤ (22853551644377/50000000000000 : ℝ)^415
        have hw : |(1374278903/2500000000 : ℝ)|=(1374278903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610218651/2500000000 : ℝ)|^543 ≤ (15799517718191/100000000000000 : ℝ)^415
        have hw : |(-610218651/2500000000 : ℝ)|=(610218651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205207797/2500000000 : ℝ)|^543 ≤ (19246689488873/50000000000000 : ℝ)^415
        have hw : |(1205207797/2500000000 : ℝ)|=(1205207797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2748557727/5000000000 : ℝ)*x 0 + (4820830383/10000000000 : ℝ)*x 1 + (-12204379/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748557727/5000000000 : ℝ)^543 ≤ (22853550784913/50000000000000 : ℝ)^415 := by
    have hnat : (2748557727 : ℕ)^543*50000000000000^415 ≤ 22853550784913^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748557727 5000000000 22853550784913 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820830383/10000000000 : ℝ)^543 ≤ (38493370567441/100000000000000 : ℝ)^415 := by
    have hnat : (4820830383 : ℕ)^543*100000000000000^415 ≤ 38493370567441^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820830383 10000000000 38493370567441 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12204379/50000000 : ℝ)^543 ≤ (3159905569507/20000000000000 : ℝ)^415 := by
    have hnat : (12204379 : ℕ)^543*20000000000000^415 ≤ 3159905569507^415*50000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12204379 50000000 3159905569507 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748557727/5000000000 : ℝ), (4820830383/10000000000 : ℝ), (-12204379/50000000 : ℝ)] ![(22853550784913/50000000000000 : ℝ), (38493370567441/100000000000000 : ℝ), (3159905569507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748557727/5000000000 : ℝ)|^543 ≤ (22853550784913/50000000000000 : ℝ)^415
        have hw : |(2748557727/5000000000 : ℝ)|=(2748557727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820830383/10000000000 : ℝ)|^543 ≤ (38493370567441/100000000000000 : ℝ)^415
        have hw : |(4820830383/10000000000 : ℝ)|=(4820830383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12204379/50000000 : ℝ)|^543 ≤ (3159905569507/20000000000000 : ℝ)^415
        have hw : |(-12204379/50000000 : ℝ)|=(12204379/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (33380213/80000000 : ℝ)*x 0 + (310474453/1000000000 : ℝ)*x 1 + (5568946969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33380213/80000000 : ℝ)^543 ≤ (796631375191/2500000000000 : ℝ)^415 := by
    have hnat : (33380213 : ℕ)^543*2500000000000^415 ≤ 796631375191^415*80000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33380213 80000000 796631375191 2500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310474453/1000000000 : ℝ)^543 ≤ (5411149356099/25000000000000 : ℝ)^415 := by
    have hnat : (310474453 : ℕ)^543*25000000000000^415 ≤ 5411149356099^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310474453 1000000000 5411149356099 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5568946969/10000000000 : ℝ)^543 ≤ (23245073774329/50000000000000 : ℝ)^415 := by
    have hnat : (5568946969 : ℕ)^543*50000000000000^415 ≤ 23245073774329^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5568946969 10000000000 23245073774329 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33380213/80000000 : ℝ), (310474453/1000000000 : ℝ), (5568946969/10000000000 : ℝ)] ![(796631375191/2500000000000 : ℝ), (5411149356099/25000000000000 : ℝ), (23245073774329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33380213/80000000 : ℝ)|^543 ≤ (796631375191/2500000000000 : ℝ)^415
        have hw : |(33380213/80000000 : ℝ)|=(33380213/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(310474453/1000000000 : ℝ)|^543 ≤ (5411149356099/25000000000000 : ℝ)^415
        have hw : |(310474453/1000000000 : ℝ)|=(310474453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5568946969/10000000000 : ℝ)|^543 ≤ (23245073774329/50000000000000 : ℝ)^415
        have hw : |(5568946969/10000000000 : ℝ)|=(5568946969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-44720399/250000000 : ℝ)*x 0 + (4850558927/10000000000 : ℝ)*x 1 + (2974091383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44720399/250000000 : ℝ)^543 ≤ (10520386523047/100000000000000 : ℝ)^415 := by
    have hnat : (44720399 : ℕ)^543*100000000000000^415 ≤ 10520386523047^415*250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44720399 250000000 10520386523047 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4850558927/10000000000 : ℝ)^543 ≤ (38804256948381/100000000000000 : ℝ)^415 := by
    have hnat : (4850558927 : ℕ)^543*100000000000000^415 ≤ 38804256948381^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850558927 10000000000 38804256948381 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2974091383/5000000000 : ℝ)^543 ≤ (5067535650501/10000000000000 : ℝ)^415 := by
    have hnat : (2974091383 : ℕ)^543*10000000000000^415 ≤ 5067535650501^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974091383 5000000000 5067535650501 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44720399/250000000 : ℝ), (4850558927/10000000000 : ℝ), (2974091383/5000000000 : ℝ)] ![(10520386523047/100000000000000 : ℝ), (38804256948381/100000000000000 : ℝ), (5067535650501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44720399/250000000 : ℝ)|^543 ≤ (10520386523047/100000000000000 : ℝ)^415
        have hw : |(-44720399/250000000 : ℝ)|=(44720399/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4850558927/10000000000 : ℝ)|^543 ≤ (38804256948381/100000000000000 : ℝ)^415
        have hw : |(4850558927/10000000000 : ℝ)|=(4850558927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2974091383/5000000000 : ℝ)|^543 ≤ (5067535650501/10000000000000 : ℝ)^415
        have hw : |(2974091383/5000000000 : ℝ)|=(2974091383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1295309717/2500000000 : ℝ)*x 0 + (-262704741/2000000000 : ℝ)*x 1 + (5948182593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295309717/2500000000 : ℝ)^543 ≤ (5287681904577/12500000000000 : ℝ)^415 := by
    have hnat : (1295309717 : ℕ)^543*12500000000000^415 ≤ 5287681904577^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295309717 2500000000 5287681904577 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262704741/2000000000 : ℝ)^543 ≤ (175579754327/2500000000000 : ℝ)^415 := by
    have hnat : (262704741 : ℕ)^543*2500000000000^415 ≤ 175579754327^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262704741 2000000000 175579754327 2500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5948182593/10000000000 : ℝ)^543 ≤ (50675354576551/100000000000000 : ℝ)^415 := by
    have hnat : (5948182593 : ℕ)^543*100000000000000^415 ≤ 50675354576551^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948182593 10000000000 50675354576551 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295309717/2500000000 : ℝ), (-262704741/2000000000 : ℝ), (5948182593/10000000000 : ℝ)] ![(5287681904577/12500000000000 : ℝ), (175579754327/2500000000000 : ℝ), (50675354576551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295309717/2500000000 : ℝ)|^543 ≤ (5287681904577/12500000000000 : ℝ)^415
        have hw : |(1295309717/2500000000 : ℝ)|=(1295309717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262704741/2000000000 : ℝ)|^543 ≤ (175579754327/2500000000000 : ℝ)^415
        have hw : |(-262704741/2000000000 : ℝ)|=(262704741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5948182593/10000000000 : ℝ)|^543 ≤ (50675354576551/100000000000000 : ℝ)^415
        have hw : |(5948182593/10000000000 : ℝ)|=(5948182593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (647654817/1250000000 : ℝ)*x 0 + (5948182721/10000000000 : ℝ)*x 1 + (-1313524007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647654817/1250000000 : ℝ)^543 ≤ (42301451690021/100000000000000 : ℝ)^415 := by
    have hnat : (647654817 : ℕ)^543*100000000000000^415 ≤ 42301451690021^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647654817 1250000000 42301451690021 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5948182721/10000000000 : ℝ)^543 ≤ (50675356003387/100000000000000 : ℝ)^415 := by
    have hnat : (5948182721 : ℕ)^543*100000000000000^415 ≤ 50675356003387^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948182721 10000000000 50675356003387 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313524007/10000000000 : ℝ)^543 ≤ (1404638457173/20000000000000 : ℝ)^415 := by
    have hnat : (1313524007 : ℕ)^543*20000000000000^415 ≤ 1404638457173^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313524007 10000000000 1404638457173 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647654817/1250000000 : ℝ), (5948182721/10000000000 : ℝ), (-1313524007/10000000000 : ℝ)] ![(42301451690021/100000000000000 : ℝ), (50675356003387/100000000000000 : ℝ), (1404638457173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647654817/1250000000 : ℝ)|^543 ≤ (42301451690021/100000000000000 : ℝ)^415
        have hw : |(647654817/1250000000 : ℝ)|=(647654817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5948182721/10000000000 : ℝ)|^543 ≤ (50675356003387/100000000000000 : ℝ)^415
        have hw : |(5948182721/10000000000 : ℝ)|=(5948182721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1313524007/10000000000 : ℝ)|^543 ≤ (1404638457173/20000000000000 : ℝ)^415
        have hw : |(-1313524007/10000000000 : ℝ)|=(1313524007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s0_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2090773599/5000000000 : ℝ)*x 0 + (1376423219/2500000000 : ℝ)*x 1 + (396282401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090773599/5000000000 : ℝ)^543 ≤ (15977711130241/50000000000000 : ℝ)^415 := by
    have hnat : (2090773599 : ℕ)^543*50000000000000^415 ≤ 15977711130241^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090773599 5000000000 15977711130241 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376423219/2500000000 : ℝ)^543 ≤ (143126375871/312500000000 : ℝ)^415 := by
    have hnat : (1376423219 : ℕ)^543*312500000000^415 ≤ 143126375871^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376423219 2500000000 143126375871 312500000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396282401/1250000000 : ℝ)^543 ≤ (2780517181139/12500000000000 : ℝ)^415 := by
    have hnat : (396282401 : ℕ)^543*12500000000000^415 ≤ 2780517181139^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396282401 1250000000 2780517181139 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090773599/5000000000 : ℝ), (1376423219/2500000000 : ℝ), (396282401/1250000000 : ℝ)] ![(15977711130241/50000000000000 : ℝ), (143126375871/312500000000 : ℝ), (2780517181139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090773599/5000000000 : ℝ)|^543 ≤ (15977711130241/50000000000000 : ℝ)^415
        have hw : |(2090773599/5000000000 : ℝ)|=(2090773599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376423219/2500000000 : ℝ)|^543 ≤ (143126375871/312500000000 : ℝ)^415
        have hw : |(1376423219/2500000000 : ℝ)|=(1376423219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396282401/1250000000 : ℝ)|^543 ≤ (2780517181139/12500000000000 : ℝ)^415
        have hw : |(396282401/1250000000 : ℝ)|=(396282401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (69/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6643/25000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (4343/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4343 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4343*1^1024 ≤ 0^1024*1^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4343/1024 : ℝ) ≤ (2052354995359247073/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4343 ≤ (2052354995359247073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4343*100000000000000000000^1024 ≤ 2052354995359247073^1024*5^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2052354995359247073 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2052354995359247073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4343 := by
      have hnat : (1 : ℕ)^1024*1^4343 ≤ 1^4343*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102052354995359247073/100000000000000000000 : ℝ) ≤ (10048015802950637/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (102052354995359247073/100000000000000000000 : ℝ)^1024 ≤ (10048015802950637/10000000000000000 : ℝ)^4343 := by
      have hnat : (102052354995359247073 : ℕ)^1024*10000000000000000^4343 ≤ 10048015802950637^4343*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102052354995359247073 100000000000000000000 10048015802950637 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048015802950637/10000000000000000 : ℝ)) (X := (102052354995359247073/100000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52052354995359247073/50000000000000000000 : ℝ) ≤ (5048015802950637/5000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (52052354995359247073/50000000000000000000 : ℝ)^1024 ≤ (5048015802950637/5000000000000000 : ℝ)^4343 := by
      have hnat : (52052354995359247073 : ℕ)^1024*5000000000000000^4343 ≤ 5048015802950637^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52052354995359247073 50000000000000000000 5048015802950637 5000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048015802950637/5000000000000000 : ℝ)) (X := (52052354995359247073/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48015802950637/4000000000000000 : ℝ)*(0 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48015802950637/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2052354995359247073/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48015802950637/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48015802950637/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048015802950637/10000000000000000 : ℝ) by norm_num, show 1+(2052354995359247073/100000000000000000000 : ℝ)+(0 : ℝ)=(102052354995359247073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2052354995359247073/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48015802950637/4000000000000000 : ℝ)*(2/5 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48015802950637/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048015802950637/5000000000000000 : ℝ) by norm_num, show 1+2*(2052354995359247073/100000000000000000000 : ℝ)=(52052354995359247073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48015802950637/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48015802950637/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48015802950637/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48015802950637/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48015802950637/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48015802950637/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1784575239/10000000000 : ℝ)*X 0 0+(1195794763/2000000000 : ℝ)*X 0 1+(1205207621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374278903/2500000000 : ℝ)*X 1 0+(-610218651/2500000000 : ℝ)*X 1 1+(1205207797/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748557727/5000000000 : ℝ)*X 2 0+(4820830383/10000000000 : ℝ)*X 2 1+(-12204379/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33380213/80000000 : ℝ)*X 0 0+(310474453/1000000000 : ℝ)*X 0 1+(5568946969/10000000000 : ℝ)*X 0 2+(33380213/80000000 : ℝ)*X 1 0+(310474453/1000000000 : ℝ)*X 1 1+(5568946969/10000000000 : ℝ)*X 1 2+(33380213/80000000 : ℝ)*X 2 0+(310474453/1000000000 : ℝ)*X 2 1+(5568946969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44720399/250000000 : ℝ)*X 0 0+(4850558927/10000000000 : ℝ)*X 0 1+(2974091383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1295309717/2500000000 : ℝ)*X 1 0+(-262704741/2000000000 : ℝ)*X 1 1+(5948182593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647654817/1250000000 : ℝ)*X 2 0+(5948182721/10000000000 : ℝ)*X 2 1+(-1313524007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2090773599/5000000000 : ℝ)*X 0 0+(1376423219/2500000000 : ℝ)*X 0 1+(396282401/1250000000 : ℝ)*X 0 2+(2090773599/5000000000 : ℝ)*X 1 0+(1376423219/2500000000 : ℝ)*X 1 1+(396282401/1250000000 : ℝ)*X 1 2+(2090773599/5000000000 : ℝ)*X 2 0+(1376423219/2500000000 : ℝ)*X 2 1+(396282401/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96686457553584979261131/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123284233/50000000000000 : ℝ)*(base1) + (27530971/50000000000000 : ℝ)*(base16) + (106561591/12500000000000 : ℝ)*(base19) + (441368479/50000000000000 : ℝ)*(base23) + (135940981/100000000000000 : ℝ)*(upper3) + (317317130738979/50000000000000 : ℝ)*(major0) + (317317130738979/50000000000000 : ℝ)*(major1) + (317317130738979/50000000000000 : ℝ)*(major2) + (43172689033267/5000000000000 : ℝ)*(sp0) + (34538183459809/4000000000000 : ℝ)*(sp1) + (107931826414117/12500000000000 : ℝ)*(sp2) + (202905769679237/50000000000000 : ℝ)*(sp3) + (97997651/5000000000000 : ℝ)*(sp4) + (111406379/10000000000000 : ℝ)*(sp7) + (40581289999073/10000000000000 : ℝ)*(f.failure) + (172691098809979/20000000000000 : ℝ)*(f.sum) + (142918947779623/100000000000000000000000000000 : ℝ)*base65 + (2599982688779623/200000000000000000000000000000 : ℝ)*base67 + (1706256167579623/200000000000000000000000000000 : ℝ)*base69 + (1661943794779623/200000000000000000000000000000 : ℝ)*base71 + (554216332779623/100000000000000000000000000000 : ℝ)*base73 + (2169216283579623/200000000000000000000000000000 : ℝ)*base75 + (2060991745979623/200000000000000000000000000000 : ℝ)*base77 + (2881972119179623/200000000000000000000000000000 : ℝ)*base79 + (147869013820377/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (4876701/500000000000000000000 : ℝ)*base90 + (4876701/500000000000000000000 : ℝ)*base92 + (4876701/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76001975053378222375503/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (750060901/50000000000000 : ℝ)*(base19) + (1439574511/100000000000000 : ℝ)*(base23) + (144113937/100000000000000 : ℝ)*(base32) + (103847851/50000000000000 : ℝ)*(upper3) + (140502503/100000000000000 : ℝ)*(upper5) + (41851383773927/6250000000000 : ℝ)*(major0) + (41851383773927/6250000000000 : ℝ)*(major1) + (41851383773927/6250000000000 : ℝ)*(major2) + (681890223/20000000000000 : ℝ)*(sp1) + (3373868703/100000000000000 : ℝ)*(sp2) + (911058398275683/100000000000000 : ℝ)*(sp4) + (455526744351383/50000000000000 : ℝ)*(sp5) + (91105358483247/10000000000000 : ℝ)*(sp6) + (4281855357041/1000000000000 : ℝ)*(sp7) + (107046419954509/25000000000000 : ℝ)*(f.failure) + (911058398275683/100000000000000 : ℝ)*(f.sum) + (10511490358501/12500000000000000000000000000 : ℝ)*base66 + (594555116499/25000000000000000000000000000 : ℝ)*base67 + (227365349191499/25000000000000000000000000000 : ℝ)*base69 + (89817946941499/25000000000000000000000000000 : ℝ)*base71 + (59375602733501/12500000000000000000000000000 : ℝ)*base74 + (170164157191499/25000000000000000000000000000 : ℝ)*base75 + (15300851591499/25000000000000000000000000000 : ℝ)*base77 + (45062494333501/25000000000000000000000000000 : ℝ)*base80 + (42509172266499/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16079833/1250000000000000000000 : ℝ)*base90 + (16079833/1250000000000000000000 : ℝ)*base92 + (16079833/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1384_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6643/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_s1_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-196334857/1000000000 : ℝ)*x 0 + (562379453/1000000000 : ℝ)*x 1 + (5061472303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196334857/1000000000 : ℝ)^543 ≤ (594160758703/5000000000000 : ℝ)^415 := by
    have hnat : (196334857 : ℕ)^543*5000000000000^415 ≤ 594160758703^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196334857 1000000000 594160758703 5000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562379453/1000000000 : ℝ)^543 ≤ (11772538021779/25000000000000 : ℝ)^415 := by
    have hnat : (562379453 : ℕ)^543*25000000000000^415 ≤ 11772538021779^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562379453 1000000000 11772538021779 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5061472303/10000000000 : ℝ)^543 ≤ (8205326544663/20000000000000 : ℝ)^415 := by
    have hnat : (5061472303 : ℕ)^543*20000000000000^415 ≤ 8205326544663^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061472303 10000000000 8205326544663 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196334857/1000000000 : ℝ), (562379453/1000000000 : ℝ), (5061472303/10000000000 : ℝ)] ![(594160758703/5000000000000 : ℝ), (11772538021779/25000000000000 : ℝ), (8205326544663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196334857/1000000000 : ℝ)|^543 ≤ (594160758703/5000000000000 : ℝ)^415
        have hw : |(-196334857/1000000000 : ℝ)|=(196334857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562379453/1000000000 : ℝ)|^543 ≤ (11772538021779/25000000000000 : ℝ)^415
        have hw : |(562379453/1000000000 : ℝ)|=(562379453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5061472303/10000000000 : ℝ)|^543 ≤ (8205326544663/20000000000000 : ℝ)^415
        have hw : |(5061472303/10000000000 : ℝ)|=(5061472303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (540137389/1000000000 : ℝ)*x 0 + (-2262369371/10000000000 : ℝ)*x 1 + (5061473747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540137389/1000000000 : ℝ)^543 ≤ (8933662064439/20000000000000 : ℝ)^415 := by
    have hnat : (540137389 : ℕ)^543*20000000000000^415 ≤ 8933662064439^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540137389 1000000000 8933662064439 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262369371/10000000000 : ℝ)^543 ≤ (7152520814241/50000000000000 : ℝ)^415 := by
    have hnat : (2262369371 : ℕ)^543*50000000000000^415 ≤ 7152520814241^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262369371 10000000000 7152520814241 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5061473747/10000000000 : ℝ)^543 ≤ (10256662009499/25000000000000 : ℝ)^415 := by
    have hnat : (5061473747 : ℕ)^543*25000000000000^415 ≤ 10256662009499^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061473747 10000000000 10256662009499 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540137389/1000000000 : ℝ), (-2262369371/10000000000 : ℝ), (5061473747/10000000000 : ℝ)] ![(8933662064439/20000000000000 : ℝ), (7152520814241/50000000000000 : ℝ), (10256662009499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540137389/1000000000 : ℝ)|^543 ≤ (8933662064439/20000000000000 : ℝ)^415
        have hw : |(540137389/1000000000 : ℝ)|=(540137389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2262369371/10000000000 : ℝ)|^543 ≤ (7152520814241/50000000000000 : ℝ)^415
        have hw : |(-2262369371/10000000000 : ℝ)|=(2262369371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5061473747/10000000000 : ℝ)|^543 ≤ (10256662009499/25000000000000 : ℝ)^415
        have hw : |(5061473747/10000000000 : ℝ)|=(5061473747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5401374647/10000000000 : ℝ)*x 0 + (2530736243/5000000000 : ℝ)*x 1 + (-2262369997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401374647/10000000000 : ℝ)^543 ≤ (11167079628327/25000000000000 : ℝ)^415 := by
    have hnat : (5401374647 : ℕ)^543*25000000000000^415 ≤ 11167079628327^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401374647 10000000000 11167079628327 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530736243/5000000000 : ℝ)^543 ≤ (10256658666041/25000000000000 : ℝ)^415 := by
    have hnat : (2530736243 : ℕ)^543*25000000000000^415 ≤ 10256658666041^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530736243 5000000000 10256658666041 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262369997/10000000000 : ℝ)^543 ≤ (14305046807551/100000000000000 : ℝ)^415 := by
    have hnat : (2262369997 : ℕ)^543*100000000000000^415 ≤ 14305046807551^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262369997 10000000000 14305046807551 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401374647/10000000000 : ℝ), (2530736243/5000000000 : ℝ), (-2262369997/10000000000 : ℝ)] ![(11167079628327/25000000000000 : ℝ), (10256658666041/25000000000000 : ℝ), (14305046807551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401374647/10000000000 : ℝ)|^543 ≤ (11167079628327/25000000000000 : ℝ)^415
        have hw : |(5401374647/10000000000 : ℝ)|=(5401374647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530736243/5000000000 : ℝ)|^543 ≤ (10256658666041/25000000000000 : ℝ)^415
        have hw : |(2530736243/5000000000 : ℝ)|=(2530736243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262369997/10000000000 : ℝ)|^543 ≤ (14305046807551/100000000000000 : ℝ)^415
        have hw : |(-2262369997/10000000000 : ℝ)|=(2262369997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (535597813/1250000000 : ℝ)*x 0 + (1862278771/5000000000 : ℝ)*x 1 + (246050817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535597813/1250000000 : ℝ)^543 ≤ (32991586582201/100000000000000 : ℝ)^415 := by
    have hnat : (535597813 : ℕ)^543*100000000000000^415 ≤ 32991586582201^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535597813 1250000000 32991586582201 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862278771/5000000000 : ℝ)^543 ≤ (13732501547927/50000000000000 : ℝ)^415 := by
    have hnat : (1862278771 : ℕ)^543*50000000000000^415 ≤ 13732501547927^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862278771 5000000000 13732501547927 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246050817/500000000 : ℝ)^543 ≤ (9885852577229/25000000000000 : ℝ)^415 := by
    have hnat : (246050817 : ℕ)^543*25000000000000^415 ≤ 9885852577229^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246050817 500000000 9885852577229 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535597813/1250000000 : ℝ), (1862278771/5000000000 : ℝ), (246050817/500000000 : ℝ)] ![(32991586582201/100000000000000 : ℝ), (13732501547927/50000000000000 : ℝ), (9885852577229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535597813/1250000000 : ℝ)|^543 ≤ (32991586582201/100000000000000 : ℝ)^415
        have hw : |(535597813/1250000000 : ℝ)|=(535597813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862278771/5000000000 : ℝ)|^543 ≤ (13732501547927/50000000000000 : ℝ)^415
        have hw : |(1862278771/5000000000 : ℝ)|=(1862278771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(246050817/500000000 : ℝ)|^543 ≤ (9885852577229/25000000000000 : ℝ)^415
        have hw : |(246050817/500000000 : ℝ)|=(246050817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-15342291/78125000 : ℝ)*x 0 + (633537871/1250000000 : ℝ)*x 1 + (1404210913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15342291/78125000 : ℝ)^543 ≤ (1485861905683/12500000000000 : ℝ)^415 := by
    have hnat : (15342291 : ℕ)^543*12500000000000^415 ≤ 1485861905683^415*78125000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15342291 78125000 1485861905683 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633537871/1250000000 : ℝ)^543 ≤ (1643963680551/4000000000000 : ℝ)^415 := by
    have hnat : (633537871 : ℕ)^543*4000000000000^415 ≤ 1643963680551^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633537871 1250000000 1643963680551 4000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404210913/2500000000 : ℝ)^543 ≤ (4701401272479/10000000000000 : ℝ)^415 := by
    have hnat : (1404210913 : ℕ)^543*10000000000000^415 ≤ 4701401272479^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404210913 2500000000 4701401272479 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15342291/78125000 : ℝ), (633537871/1250000000 : ℝ), (1404210913/2500000000 : ℝ)] ![(1485861905683/12500000000000 : ℝ), (1643963680551/4000000000000 : ℝ), (4701401272479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15342291/78125000 : ℝ)|^543 ≤ (1485861905683/12500000000000 : ℝ)^415
        have hw : |(-15342291/78125000 : ℝ)|=(15342291/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(633537871/1250000000 : ℝ)|^543 ≤ (1643963680551/4000000000000 : ℝ)^415
        have hw : |(633537871/1250000000 : ℝ)|=(633537871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404210913/2500000000 : ℝ)|^543 ≤ (4701401272479/10000000000000 : ℝ)^415
        have hw : |(1404210913/2500000000 : ℝ)|=(1404210913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5254959959/10000000000 : ℝ)*x 0 + (-1706999259/10000000000 : ℝ)*x 1 + (140421093/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254959959/10000000000 : ℝ)^543 ≤ (43090704154043/100000000000000 : ℝ)^415 := by
    have hnat : (5254959959 : ℕ)^543*100000000000000^415 ≤ 43090704154043^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254959959 10000000000 43090704154043 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1706999259/10000000000 : ℝ)^543 ≤ (9895282372951/100000000000000 : ℝ)^415 := by
    have hnat : (1706999259 : ℕ)^543*100000000000000^415 ≤ 9895282372951^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706999259 10000000000 9895282372951 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140421093/250000000 : ℝ)^543 ≤ (23507006734757/50000000000000 : ℝ)^415 := by
    have hnat : (140421093 : ℕ)^543*50000000000000^415 ≤ 23507006734757^415*250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140421093 250000000 23507006734757 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254959959/10000000000 : ℝ), (-1706999259/10000000000 : ℝ), (140421093/250000000 : ℝ)] ![(43090704154043/100000000000000 : ℝ), (9895282372951/100000000000000 : ℝ), (23507006734757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254959959/10000000000 : ℝ)|^543 ≤ (43090704154043/100000000000000 : ℝ)^415
        have hw : |(5254959959/10000000000 : ℝ)|=(5254959959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1706999259/10000000000 : ℝ)|^543 ≤ (9895282372951/100000000000000 : ℝ)^415
        have hw : |(-1706999259/10000000000 : ℝ)|=(1706999259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140421093/250000000 : ℝ)|^543 ≤ (23507006734757/50000000000000 : ℝ)^415
        have hw : |(140421093/250000000 : ℝ)|=(140421093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (656870039/1250000000 : ℝ)*x 0 + (5616844043/10000000000 : ℝ)*x 1 + (-426749573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656870039/1250000000 : ℝ)^543 ≤ (43090707941439/100000000000000 : ℝ)^415 := by
    have hnat : (656870039 : ℕ)^543*100000000000000^415 ≤ 43090707941439^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656870039 1250000000 43090707941439 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616844043/10000000000 : ℝ)^543 ≤ (9402803401391/20000000000000 : ℝ)^415 := by
    have hnat : (5616844043 : ℕ)^543*20000000000000^415 ≤ 9402803401391^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616844043 10000000000 9402803401391 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426749573/2500000000 : ℝ)^543 ≤ (9895275038409/100000000000000 : ℝ)^415 := by
    have hnat : (426749573 : ℕ)^543*100000000000000^415 ≤ 9895275038409^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426749573 2500000000 9895275038409 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656870039/1250000000 : ℝ), (5616844043/10000000000 : ℝ), (-426749573/2500000000 : ℝ)] ![(43090707941439/100000000000000 : ℝ), (9402803401391/20000000000000 : ℝ), (9895275038409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656870039/1250000000 : ℝ)|^543 ≤ (43090707941439/100000000000000 : ℝ)^415
        have hw : |(656870039/1250000000 : ℝ)|=(656870039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616844043/10000000000 : ℝ)|^543 ≤ (9402803401391/20000000000000 : ℝ)^415
        have hw : |(5616844043/10000000000 : ℝ)|=(5616844043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426749573/2500000000 : ℝ)|^543 ≤ (9895275038409/100000000000000 : ℝ)^415
        have hw : |(-426749573/2500000000 : ℝ)|=(426749573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s1_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (53572159/125000000 : ℝ)*x 0 + (4906483531/10000000000 : ℝ)*x 1 + (1869671983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53572159/125000000 : ℝ)^543 ≤ (33001562929713/100000000000000 : ℝ)^415 := by
    have hnat : (53572159 : ℕ)^543*100000000000000^415 ≤ 33001562929713^415*125000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53572159 125000000 33001562929713 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906483531/10000000000 : ℝ)^543 ≤ (7878136182199/20000000000000 : ℝ)^415 := by
    have hnat : (4906483531 : ℕ)^543*20000000000000^415 ≤ 7878136182199^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906483531 10000000000 7878136182199 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869671983/5000000000 : ℝ)^543 ≤ (13803878076853/50000000000000 : ℝ)^415 := by
    have hnat : (1869671983 : ℕ)^543*50000000000000^415 ≤ 13803878076853^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869671983 5000000000 13803878076853 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53572159/125000000 : ℝ), (4906483531/10000000000 : ℝ), (1869671983/5000000000 : ℝ)] ![(33001562929713/100000000000000 : ℝ), (7878136182199/20000000000000 : ℝ), (13803878076853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53572159/125000000 : ℝ)|^543 ≤ (33001562929713/100000000000000 : ℝ)^415
        have hw : |(53572159/125000000 : ℝ)|=(53572159/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906483531/10000000000 : ℝ)|^543 ≤ (7878136182199/20000000000000 : ℝ)^415
        have hw : |(4906483531/10000000000 : ℝ)|=(4906483531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1869671983/5000000000 : ℝ)|^543 ≤ (13803878076853/50000000000000 : ℝ)^415
        have hw : |(1869671983/5000000000 : ℝ)|=(1869671983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6643/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (7269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3831/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6643/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (69/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6643/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (69/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6643/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (69/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6643/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (69/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6643/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (69/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6643/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (69/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (69/4000 : ℝ) ^ (4343/1024 : ℝ) ≤ (3325451691741/100000000000000000000 : ℝ) := by
    have hpowers : (69/4000 : ℝ)^4343 ≤ (3325451691741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (69 : ℕ)^4343*100000000000000000000^1024 ≤ 3325451691741^1024*4000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 4000 3325451691741 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/4000 : ℝ)) (X := (3325451691741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6643/25000 : ℝ) ^ (4343/1024 : ℝ) ≤ (362127750880978953/100000000000000000000 : ℝ) := by
    have hpowers : (6643/25000 : ℝ)^4343 ≤ (362127750880978953/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6643 : ℕ)^4343*100000000000000000000^1024 ≤ 362127750880978953^1024*25000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6643 25000 362127750880978953 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6643/25000 : ℝ)) (X := (362127750880978953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003325451691741/50000000000000000000 : ℝ) ≤ (10000000156816139/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50000003325451691741/50000000000000000000 : ℝ)^1024 ≤ (10000000156816139/10000000000000000 : ℝ)^4343 := by
      have hnat : (50000003325451691741 : ℕ)^1024*10000000000000000^4343 ≤ 10000000156816139^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003325451691741 50000000000000000000 10000000156816139 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000156816139/10000000000000000 : ℝ)) (X := (50000003325451691741/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50181065538166335347/50000000000000000000 : ℝ) ≤ (10008526598943973/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50181065538166335347/50000000000000000000 : ℝ)^1024 ≤ (10008526598943973/10000000000000000 : ℝ)^4343 := by
      have hnat : (50181065538166335347 : ℕ)^1024*10000000000000000^4343 ≤ 10008526598943973^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181065538166335347 50000000000000000000 10008526598943973 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008526598943973/10000000000000000 : ℝ)) (X := (50181065538166335347/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50362127750880978953/50000000000000000000 : ℝ) ≤ (10017053041071807/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50362127750880978953/50000000000000000000 : ℝ)^1024 ≤ (10017053041071807/10000000000000000 : ℝ)^4343 := by
      have hnat : (50362127750880978953 : ℕ)^1024*10000000000000000^4343 ≤ 10017053041071807^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50362127750880978953 50000000000000000000 10017053041071807 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017053041071807/10000000000000000 : ℝ)) (X := (50362127750880978953/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3325451691741/100000000000000000000 : ℝ) ≤ ((248440587671069578433/248470000000000000000 : ℝ)+2*(4263221063917/1242350000000000 : ℝ)*(69/4000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (248440587671069578433/248470000000000000000 : ℝ)+2*(4263221063917/1242350000000000 : ℝ)*(69/4000 : ℝ)=(10000000156816139/10000000000000000 : ℝ) by norm_num, show 1+2*(3325451691741/100000000000000000000 : ℝ)=(50000003325451691741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(362127750880978953/100000000000000000000 : ℝ)+(3325451691741/100000000000000000000 : ℝ) ≤ ((248440587671069578433/248470000000000000000 : ℝ)+(4263221063917/1242350000000000 : ℝ)*((6643/25000 : ℝ)+(69/4000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (248440587671069578433/248470000000000000000 : ℝ)+(4263221063917/1242350000000000 : ℝ)*((6643/25000 : ℝ)+(69/4000 : ℝ))=(10008526598943973/10000000000000000 : ℝ) by norm_num, show 1+(362127750880978953/100000000000000000000 : ℝ)+(3325451691741/100000000000000000000 : ℝ)=(50181065538166335347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(362127750880978953/100000000000000000000 : ℝ) ≤ ((248440587671069578433/248470000000000000000 : ℝ)+2*(4263221063917/1242350000000000 : ℝ)*(6643/25000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (248440587671069578433/248470000000000000000 : ℝ)+2*(4263221063917/1242350000000000 : ℝ)*(6643/25000 : ℝ)=(10017053041071807/10000000000000000 : ℝ) by norm_num, show 1+2*(362127750880978953/100000000000000000000 : ℝ)=(50362127750880978953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (248440587671069578433/248470000000000000000 : ℝ)*(X 1 0+X 2 0)+(4263221063917/1242350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (69/4000 : ℝ)) (hi := (6643/25000 : ℝ)) (c := (248440587671069578433/248470000000000000000 : ℝ)) (alpha := (4263221063917/1242350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (248440587671069578433/248470000000000000000 : ℝ)*(X 0 1+X 2 1)+(4263221063917/1242350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (69/4000 : ℝ)) (hi := (6643/25000 : ℝ)) (c := (248440587671069578433/248470000000000000000 : ℝ)) (alpha := (4263221063917/1242350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (248440587671069578433/248470000000000000000 : ℝ)*(X 0 2+X 1 2)+(4263221063917/1242350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (69/4000 : ℝ)) (hi := (6643/25000 : ℝ)) (c := (248440587671069578433/248470000000000000000 : ℝ)) (alpha := (4263221063917/1242350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196334857/1000000000 : ℝ)*X 0 0+(562379453/1000000000 : ℝ)*X 0 1+(5061472303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((540137389/1000000000 : ℝ)*X 1 0+(-2262369371/10000000000 : ℝ)*X 1 1+(5061473747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5401374647/10000000000 : ℝ)*X 2 0+(2530736243/5000000000 : ℝ)*X 2 1+(-2262369997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535597813/1250000000 : ℝ)*X 0 0+(1862278771/5000000000 : ℝ)*X 0 1+(246050817/500000000 : ℝ)*X 0 2+(535597813/1250000000 : ℝ)*X 1 0+(1862278771/5000000000 : ℝ)*X 1 1+(246050817/500000000 : ℝ)*X 1 2+(535597813/1250000000 : ℝ)*X 2 0+(1862278771/5000000000 : ℝ)*X 2 1+(246050817/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15342291/78125000 : ℝ)*X 0 0+(633537871/1250000000 : ℝ)*X 0 1+(1404210913/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254959959/10000000000 : ℝ)*X 1 0+(-1706999259/10000000000 : ℝ)*X 1 1+(140421093/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656870039/1250000000 : ℝ)*X 2 0+(5616844043/10000000000 : ℝ)*X 2 1+(-426749573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53572159/125000000 : ℝ)*X 0 0+(4906483531/10000000000 : ℝ)*X 0 1+(1869671983/5000000000 : ℝ)*X 0 2+(53572159/125000000 : ℝ)*X 1 0+(4906483531/10000000000 : ℝ)*X 1 1+(1869671983/5000000000 : ℝ)*X 1 2+(53572159/125000000 : ℝ)*X 2 0+(4906483531/10000000000 : ℝ)*X 2 1+(1869671983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23205520359233109554918502819/3105875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1260573681/100000000000000 : ℝ)*(base19) + (186230239/12500000000000 : ℝ)*(base23) + (234257361/100000000000000 : ℝ)*(upper3) + (5392881/50000000000000 : ℝ)*(upper4) + (598271/10000000000000 : ℝ)*(upper5) + (653543380123519/50000000000000 : ℝ)*(major0) + (653543380123519/50000000000000 : ℝ)*(major1) + (653543380123519/50000000000000 : ℝ)*(major2) + (222294152685887/12500000000000 : ℝ)*(sp0) + (1778363576135271/100000000000000 : ℝ)*(sp1) + (11114770917919/625000000000 : ℝ)*(sp2) + (835803339384827/100000000000000 : ℝ)*(sp3) + (362975683/3125000000000 : ℝ)*(sp4) + (2547675279/50000000000000 : ℝ)*(sp7) + (167161686947077/20000000000000 : ℝ)*(f.failure) + (222295604588619/12500000000000 : ℝ)*(f.sum) + (94080065955227/31058750000000000000000000000 : ℝ)*base66 + (36566972979613065727/12423500000000000000000000000000000 : ℝ)*base67 + (13415316239795065727/12423500000000000000000000000000000 : ℝ)*base69 + (18928674030429934273/12423500000000000000000000000000000 : ℝ)*base72 + (151435959411193/124235000000000000000000000000 : ℝ)*base74 + (6382742650425565727/12423500000000000000000000000000000 : ℝ)*base75 + (20224474587355065727/12423500000000000000000000000000000 : ℝ)*base77 + (17104219087941065727/12423500000000000000000000000000000 : ℝ)*base79 + (62836944009597/31058750000000000000000000000 : ℝ)*base82 + (5180849/1000000000000000000000 : ℝ)*base90 + (5180849/1000000000000000000000 : ℝ)*base92 + (5180849/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48507649530809596115030627487/12423500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75174793/50000000000000 : ℝ)*(base1) + (1116796013/100000000000000 : ℝ)*(base19) + (1318823031/100000000000000 : ℝ)*(base23) + (13442557/12500000000000 : ℝ)*(upper3) + (163390761/100000000000000 : ℝ)*(upper5) + (1339907860051413/100000000000000 : ℝ)*(major0) + (1339907860051413/100000000000000 : ℝ)*(major1) + (1339907860051413/100000000000000 : ℝ)*(major2) + (1116071191/20000000000000 : ℝ)*(sp1) + (210901513/2500000000000 : ℝ)*(sp2) + (455755014762943/25000000000000 : ℝ)*(sp4) + (911506605775109/50000000000000 : ℝ)*(sp5) + (364602030763727/20000000000000 : ℝ)*(sp6) + (107099441362599/12500000000000 : ℝ)*(sp7) + (428397840625189/50000000000000 : ℝ)*(f.failure) + (364603981740437/20000000000000 : ℝ)*(f.sum) + (156737013599601/62117500000000000000000000000 : ℝ)*base65 + (73494868358695824171/24847000000000000000000000000000000 : ℝ)*base68 + (185933918303791824171/24847000000000000000000000000000000 : ℝ)*base70 + (16505577145116175829/24847000000000000000000000000000000 : ℝ)*base71 + (195590687750033/124235000000000000000000000000 : ℝ)*base74 + (133456880399638824171/24847000000000000000000000000000000 : ℝ)*base76 + (264412481629039824171/24847000000000000000000000000000000 : ℝ)*base78 + (60188582829841175829/24847000000000000000000000000000000 : ℝ)*base79 + (51624488646689/62117500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (24654993/2500000000000000000000 : ℝ)*base90 + (24654993/2500000000000000000000 : ℝ)*base92 + (24654993/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1384_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6643/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3831/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_s2_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-999988921/5000000000 : ℝ)*x 0 + (1093758261/2000000000 : ℝ)*x 1 + (207718267/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999988921/5000000000 : ℝ)^543 ≤ (12174125402329/100000000000000 : ℝ)^415 := by
    have hnat : (999988921 : ℕ)^543*100000000000000^415 ≤ 12174125402329^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999988921 5000000000 12174125402329 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093758261/2000000000 : ℝ)^543 ≤ (45399200084411/100000000000000 : ℝ)^415 := by
    have hnat : (1093758261 : ℕ)^543*100000000000000^415 ≤ 45399200084411^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093758261 2000000000 45399200084411 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207718267/400000000 : ℝ)^543 ≤ (2121333724821/5000000000000 : ℝ)^415 := by
    have hnat : (207718267 : ℕ)^543*5000000000000^415 ≤ 2121333724821^415*400000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207718267 400000000 2121333724821 5000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999988921/5000000000 : ℝ), (1093758261/2000000000 : ℝ), (207718267/400000000 : ℝ)] ![(12174125402329/100000000000000 : ℝ), (45399200084411/100000000000000 : ℝ), (2121333724821/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999988921/5000000000 : ℝ)|^543 ≤ (12174125402329/100000000000000 : ℝ)^415
        have hw : |(-999988921/5000000000 : ℝ)|=(999988921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093758261/2000000000 : ℝ)|^543 ≤ (45399200084411/100000000000000 : ℝ)^415
        have hw : |(1093758261/2000000000 : ℝ)|=(1093758261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207718267/400000000 : ℝ)|^543 ≤ (2121333724821/5000000000000 : ℝ)^415
        have hw : |(207718267/400000000 : ℝ)|=(207718267/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5363070053/10000000000 : ℝ)*x 0 + (-428438393/2000000000 : ℝ)*x 1 + (5192956611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363070053/10000000000 : ℝ)^543 ≤ (44254297967817/100000000000000 : ℝ)^415 := by
    have hnat : (5363070053 : ℕ)^543*100000000000000^415 ≤ 44254297967817^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363070053 10000000000 44254297967817 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428438393/2000000000 : ℝ)^543 ≤ (3329757052813/25000000000000 : ℝ)^415 := by
    have hnat : (428438393 : ℕ)^543*25000000000000^415 ≤ 3329757052813^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428438393 2000000000 3329757052813 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192956611/10000000000 : ℝ)^543 ≤ (42426673812263/100000000000000 : ℝ)^415 := by
    have hnat : (5192956611 : ℕ)^543*100000000000000^415 ≤ 42426673812263^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192956611 10000000000 42426673812263 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363070053/10000000000 : ℝ), (-428438393/2000000000 : ℝ), (5192956611/10000000000 : ℝ)] ![(44254297967817/100000000000000 : ℝ), (3329757052813/25000000000000 : ℝ), (42426673812263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363070053/10000000000 : ℝ)|^543 ≤ (44254297967817/100000000000000 : ℝ)^415
        have hw : |(5363070053/10000000000 : ℝ)|=(5363070053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428438393/2000000000 : ℝ)|^543 ≤ (3329757052813/25000000000000 : ℝ)^415
        have hw : |(-428438393/2000000000 : ℝ)|=(428438393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192956611/10000000000 : ℝ)|^543 ≤ (42426673812263/100000000000000 : ℝ)^415
        have hw : |(5192956611/10000000000 : ℝ)|=(5192956611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2681534957/5000000000 : ℝ)*x 0 + (5192956749/10000000000 : ℝ)*x 1 + (-66943499/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681534957/5000000000 : ℝ)^543 ≤ (44254296467067/100000000000000 : ℝ)^415 := by
    have hnat : (2681534957 : ℕ)^543*100000000000000^415 ≤ 44254296467067^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681534957 5000000000 44254296467067 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192956749/10000000000 : ℝ)^543 ≤ (42426675287477/100000000000000 : ℝ)^415 := by
    have hnat : (5192956749 : ℕ)^543*100000000000000^415 ≤ 42426675287477^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192956749 10000000000 42426675287477 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66943499/312500000 : ℝ)^543 ≤ (6659514117829/50000000000000 : ℝ)^415 := by
    have hnat : (66943499 : ℕ)^543*50000000000000^415 ≤ 6659514117829^415*312500000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66943499 312500000 6659514117829 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681534957/5000000000 : ℝ), (5192956749/10000000000 : ℝ), (-66943499/312500000 : ℝ)] ![(44254296467067/100000000000000 : ℝ), (42426675287477/100000000000000 : ℝ), (6659514117829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681534957/5000000000 : ℝ)|^543 ≤ (44254296467067/100000000000000 : ℝ)^415
        have hw : |(2681534957/5000000000 : ℝ)|=(2681534957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192956749/10000000000 : ℝ)|^543 ≤ (42426675287477/100000000000000 : ℝ)^415
        have hw : |(5192956749/10000000000 : ℝ)|=(5192956749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66943499/312500000 : ℝ)|^543 ≤ (6659514117829/50000000000000 : ℝ)^415
        have hw : |(-66943499/312500000 : ℝ)|=(66943499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (43105169/100000000 : ℝ)*x 0 + (4026209589/10000000000 : ℝ)*x 1 + (1153277067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43105169/100000000 : ℝ)^543 ≤ (16625544570859/50000000000000 : ℝ)^415 := by
    have hnat : (43105169 : ℕ)^543*50000000000000^415 ≤ 16625544570859^415*100000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43105169 100000000 16625544570859 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026209589/10000000000 : ℝ)^543 ≤ (6082233500473/20000000000000 : ℝ)^415 := by
    have hnat : (4026209589 : ℕ)^543*20000000000000^415 ≤ 6082233500473^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026209589 10000000000 6082233500473 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153277067/2500000000 : ℝ)^543 ≤ (36337743347959/100000000000000 : ℝ)^415 := by
    have hnat : (1153277067 : ℕ)^543*100000000000000^415 ≤ 36337743347959^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153277067 2500000000 36337743347959 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43105169/100000000 : ℝ), (4026209589/10000000000 : ℝ), (1153277067/2500000000 : ℝ)] ![(16625544570859/50000000000000 : ℝ), (6082233500473/20000000000000 : ℝ), (36337743347959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43105169/100000000 : ℝ)|^543 ≤ (16625544570859/50000000000000 : ℝ)^415
        have hw : |(43105169/100000000 : ℝ)|=(43105169/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026209589/10000000000 : ℝ)|^543 ≤ (6082233500473/20000000000000 : ℝ)^415
        have hw : |(4026209589/10000000000 : ℝ)|=(4026209589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1153277067/2500000000 : ℝ)|^543 ≤ (36337743347959/100000000000000 : ℝ)^415
        have hw : |(1153277067/2500000000 : ℝ)|=(1153277067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000032469/10000000000 : ℝ)*x 0 + (649326239/1250000000 : ℝ)*x 1 + (2733562017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000032469/10000000000 : ℝ)^543 ≤ (12174560486717/100000000000000 : ℝ)^415 := by
    have hnat : (2000032469 : ℕ)^543*100000000000000^415 ≤ 12174560486717^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000032469 10000000000 12174560486717 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649326239/1250000000 : ℝ)^543 ≤ (42444348399227/100000000000000 : ℝ)^415 := by
    have hnat : (649326239 : ℕ)^543*100000000000000^415 ≤ 42444348399227^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649326239 1250000000 42444348399227 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733562017/5000000000 : ℝ)^543 ≤ (45381091089001/100000000000000 : ℝ)^415 := by
    have hnat : (2733562017 : ℕ)^543*100000000000000^415 ≤ 45381091089001^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733562017 5000000000 45381091089001 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000032469/10000000000 : ℝ), (649326239/1250000000 : ℝ), (2733562017/5000000000 : ℝ)] ![(12174560486717/100000000000000 : ℝ), (42444348399227/100000000000000 : ℝ), (45381091089001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000032469/10000000000 : ℝ)|^543 ≤ (12174560486717/100000000000000 : ℝ)^415
        have hw : |(-2000032469/10000000000 : ℝ)|=(2000032469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649326239/1250000000 : ℝ)|^543 ≤ (42444348399227/100000000000000 : ℝ)^415
        have hw : |(649326239/1250000000 : ℝ)|=(649326239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733562017/5000000000 : ℝ)|^543 ≤ (45381091089001/100000000000000 : ℝ)^415
        have hw : |(2733562017/5000000000 : ℝ)|=(2733562017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2645829489/5000000000 : ℝ)*x 0 + (-934012591/5000000000 : ℝ)*x 1 + (5467123721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645829489/5000000000 : ℝ)^543 ≤ (21742438681433/50000000000000 : ℝ)^415 := by
    have hnat : (2645829489 : ℕ)^543*50000000000000^415 ≤ 21742438681433^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645829489 5000000000 21742438681433 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934012591/5000000000 : ℝ)^543 ≤ (2783508732419/25000000000000 : ℝ)^415 := by
    have hnat : (934012591 : ℕ)^543*25000000000000^415 ≤ 2783508732419^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934012591 5000000000 2783508732419 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467123721/10000000000 : ℝ)^543 ≤ (11345271922381/25000000000000 : ℝ)^415 := by
    have hnat : (5467123721 : ℕ)^543*25000000000000^415 ≤ 11345271922381^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467123721 10000000000 11345271922381 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645829489/5000000000 : ℝ), (-934012591/5000000000 : ℝ), (5467123721/10000000000 : ℝ)] ![(21742438681433/50000000000000 : ℝ), (2783508732419/25000000000000 : ℝ), (11345271922381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645829489/5000000000 : ℝ)|^543 ≤ (21742438681433/50000000000000 : ℝ)^415
        have hw : |(2645829489/5000000000 : ℝ)|=(2645829489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-934012591/5000000000 : ℝ)|^543 ≤ (2783508732419/25000000000000 : ℝ)^415
        have hw : |(-934012591/5000000000 : ℝ)|=(934012591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467123721/10000000000 : ℝ)|^543 ≤ (11345271922381/25000000000000 : ℝ)^415
        have hw : |(5467123721/10000000000 : ℝ)|=(5467123721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2645830223/5000000000 : ℝ)*x 0 + (218684951/400000000 : ℝ)*x 1 + (-467005771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645830223/5000000000 : ℝ)^543 ≤ (347879145177/800000000000 : ℝ)^415 := by
    have hnat : (2645830223 : ℕ)^543*800000000000^415 ≤ 347879145177^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645830223 5000000000 347879145177 800000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218684951/400000000 : ℝ)^543 ≤ (9076217655203/20000000000000 : ℝ)^415 := by
    have hnat : (218684951 : ℕ)^543*20000000000000^415 ≤ 9076217655203^415*400000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218684951 400000000 9076217655203 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467005771/2500000000 : ℝ)^543 ≤ (1113401856803/10000000000000 : ℝ)^415 := by
    have hnat : (467005771 : ℕ)^543*10000000000000^415 ≤ 1113401856803^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467005771 2500000000 1113401856803 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645830223/5000000000 : ℝ), (218684951/400000000 : ℝ), (-467005771/2500000000 : ℝ)] ![(347879145177/800000000000 : ℝ), (9076217655203/20000000000000 : ℝ), (1113401856803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645830223/5000000000 : ℝ)|^543 ≤ (347879145177/800000000000 : ℝ)^415
        have hw : |(2645830223/5000000000 : ℝ)|=(2645830223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218684951/400000000 : ℝ)|^543 ≤ (9076217655203/20000000000000 : ℝ)^415
        have hw : |(218684951/400000000 : ℝ)|=(218684951/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467005771/2500000000 : ℝ)|^543 ≤ (1113401856803/10000000000000 : ℝ)^415
        have hw : |(-467005771/2500000000 : ℝ)|=(467005771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s2_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4310634663/10000000000 : ℝ)*x 0 + (576198901/1250000000 : ℝ)*x 1 + (2014878111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310634663/10000000000 : ℝ)^543 ≤ (8313069437633/25000000000000 : ℝ)^415 := by
    have hnat : (4310634663 : ℕ)^543*25000000000000^415 ≤ 8313069437633^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310634663 10000000000 8313069437633 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576198901/1250000000 : ℝ)^543 ≤ (18150749314299/50000000000000 : ℝ)^415 := by
    have hnat : (576198901 : ℕ)^543*50000000000000^415 ≤ 18150749314299^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576198901 1250000000 18150749314299 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014878111/5000000000 : ℝ)^543 ≤ (6089244721777/20000000000000 : ℝ)^415 := by
    have hnat : (2014878111 : ℕ)^543*20000000000000^415 ≤ 6089244721777^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014878111 5000000000 6089244721777 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310634663/10000000000 : ℝ), (576198901/1250000000 : ℝ), (2014878111/5000000000 : ℝ)] ![(8313069437633/25000000000000 : ℝ), (18150749314299/50000000000000 : ℝ), (6089244721777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310634663/10000000000 : ℝ)|^543 ≤ (8313069437633/25000000000000 : ℝ)^415
        have hw : |(4310634663/10000000000 : ℝ)|=(4310634663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576198901/1250000000 : ℝ)|^543 ≤ (18150749314299/50000000000000 : ℝ)^415
        have hw : |(576198901/1250000000 : ℝ)|=(576198901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014878111/5000000000 : ℝ)|^543 ≤ (6089244721777/20000000000000 : ℝ)^415
        have hw : |(2014878111/5000000000 : ℝ)|=(2014878111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3831/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5057/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3831/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3831/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3831/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3831/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3831/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3831/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7269/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (741726707929947/50000000000000000000 : ℝ) := by
    have hpowers : (7269/100000 : ℝ)^4343 ≤ (741726707929947/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7269 : ℕ)^4343*50000000000000000000^1024 ≤ 741726707929947^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7269 100000 741726707929947 50000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7269/100000 : ℝ)) (X := (741726707929947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3831/20000 : ℝ) ^ (4343/1024 : ℝ) ≤ (22591613007891549/25000000000000000000 : ℝ) := by
    have hpowers : (3831/20000 : ℝ)^4343 ≤ (22591613007891549/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3831 : ℕ)^4343*25000000000000000000^1024 ≤ 22591613007891549^1024*20000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3831 20000 22591613007891549 25000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3831/20000 : ℝ)) (X := (22591613007891549/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000741726707929947/25000000000000000000 : ℝ) ≤ (10000069953445861/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (25000741726707929947/25000000000000000000 : ℝ)^1024 ≤ (10000069953445861/10000000000000000 : ℝ)^4343 := by
      have hnat : (25000741726707929947 : ℕ)^1024*10000000000000000^4343 ≤ 10000069953445861^4343*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000741726707929947 25000000000000000000 10000069953445861 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000069953445861/10000000000000000 : ℝ)) (X := (25000741726707929947/25000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10009184990544742609/10000000000000000000 : ℝ) ≤ (5001082446592807/5000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (10009184990544742609/10000000000000000000 : ℝ)^1024 ≤ (5001082446592807/5000000000000000 : ℝ)^4343 := by
      have hnat : (10009184990544742609 : ℕ)^1024*5000000000000000^4343 ≤ 5001082446592807^4343*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009184990544742609 10000000000000000000 5001082446592807 5000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001082446592807/5000000000000000 : ℝ)) (X := (10009184990544742609/10000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12522591613007891549/12500000000000000000 : ℝ) ≤ (10004259832925367/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (12522591613007891549/12500000000000000000 : ℝ)^1024 ≤ (10004259832925367/10000000000000000 : ℝ)^4343 := by
      have hnat : (12522591613007891549 : ℕ)^1024*10000000000000000^4343 ≤ 10004259832925367^4343*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12522591613007891549 12500000000000000000 10004259832925367 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004259832925367/10000000000000000 : ℝ)) (X := (12522591613007891549/12500000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(741726707929947/50000000000000000000 : ℝ) ≤ ((1414647324199059223/1415000000000000000 : ℝ)+2*(299277105679/169800000000000 : ℝ)*(7269/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (1414647324199059223/1415000000000000000 : ℝ)+2*(299277105679/169800000000000 : ℝ)*(7269/100000 : ℝ)=(10000069953445861/10000000000000000 : ℝ) by norm_num, show 1+2*(741726707929947/50000000000000000000 : ℝ)=(25000741726707929947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22591613007891549/25000000000000000000 : ℝ)+(741726707929947/50000000000000000000 : ℝ) ≤ ((1414647324199059223/1415000000000000000 : ℝ)+(299277105679/169800000000000 : ℝ)*((3831/20000 : ℝ)+(7269/100000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (1414647324199059223/1415000000000000000 : ℝ)+(299277105679/169800000000000 : ℝ)*((3831/20000 : ℝ)+(7269/100000 : ℝ))=(5001082446592807/5000000000000000 : ℝ) by norm_num, show 1+(22591613007891549/25000000000000000000 : ℝ)+(741726707929947/50000000000000000000 : ℝ)=(10009184990544742609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22591613007891549/25000000000000000000 : ℝ) ≤ ((1414647324199059223/1415000000000000000 : ℝ)+2*(299277105679/169800000000000 : ℝ)*(3831/20000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (1414647324199059223/1415000000000000000 : ℝ)+2*(299277105679/169800000000000 : ℝ)*(3831/20000 : ℝ)=(10004259832925367/10000000000000000 : ℝ) by norm_num, show 1+2*(22591613007891549/25000000000000000000 : ℝ)=(12522591613007891549/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1414647324199059223/1415000000000000000 : ℝ)*(X 1 0+X 2 0)+(299277105679/169800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (7269/100000 : ℝ)) (hi := (3831/20000 : ℝ)) (c := (1414647324199059223/1415000000000000000 : ℝ)) (alpha := (299277105679/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1414647324199059223/1415000000000000000 : ℝ)*(X 0 1+X 2 1)+(299277105679/169800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (7269/100000 : ℝ)) (hi := (3831/20000 : ℝ)) (c := (1414647324199059223/1415000000000000000 : ℝ)) (alpha := (299277105679/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1414647324199059223/1415000000000000000 : ℝ)*(X 0 2+X 1 2)+(299277105679/169800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (7269/100000 : ℝ)) (hi := (3831/20000 : ℝ)) (c := (1414647324199059223/1415000000000000000 : ℝ)) (alpha := (299277105679/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-999988921/5000000000 : ℝ)*X 0 0+(1093758261/2000000000 : ℝ)*X 0 1+(207718267/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363070053/10000000000 : ℝ)*X 1 0+(-428438393/2000000000 : ℝ)*X 1 1+(5192956611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681534957/5000000000 : ℝ)*X 2 0+(5192956749/10000000000 : ℝ)*X 2 1+(-66943499/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43105169/100000000 : ℝ)*X 0 0+(4026209589/10000000000 : ℝ)*X 0 1+(1153277067/2500000000 : ℝ)*X 0 2+(43105169/100000000 : ℝ)*X 1 0+(4026209589/10000000000 : ℝ)*X 1 1+(1153277067/2500000000 : ℝ)*X 1 2+(43105169/100000000 : ℝ)*X 2 0+(4026209589/10000000000 : ℝ)*X 2 1+(1153277067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2000032469/10000000000 : ℝ)*X 0 0+(649326239/1250000000 : ℝ)*X 0 1+(2733562017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645829489/5000000000 : ℝ)*X 1 0+(-934012591/5000000000 : ℝ)*X 1 1+(5467123721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645830223/5000000000 : ℝ)*X 2 0+(218684951/400000000 : ℝ)*X 2 1+(-467005771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310634663/10000000000 : ℝ)*X 0 0+(576198901/1250000000 : ℝ)*X 0 1+(2014878111/5000000000 : ℝ)*X 0 2+(4310634663/10000000000 : ℝ)*X 1 0+(576198901/1250000000 : ℝ)*X 1 1+(2014878111/5000000000 : ℝ)*X 1 2+(4310634663/10000000000 : ℝ)*X 2 0+(576198901/1250000000 : ℝ)*X 2 1+(2014878111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187076430622506736502877171/35375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190348061/20000000000000 : ℝ)*(base19) + (188573667/25000000000000 : ℝ)*(base23) + (1387467/2500000000000 : ℝ)*(lower2) + (170627807/100000000000000 : ℝ)*(upper3) + (66437349/100000000000000 : ℝ)*(upper5) + (1332316100749547/50000000000000 : ℝ)*(major0) + (1332316100749547/50000000000000 : ℝ)*(major1) + (1332316100749547/50000000000000 : ℝ)*(major2) + (3625372252686911/100000000000000 : ℝ)*(sp0) + (3625380918263731/100000000000000 : ℝ)*(sp1) + (453172639463671/12500000000000 : ℝ)*(sp2) + (1703876432149921/100000000000000 : ℝ)*(sp3) + (76938537/800000000000 : ℝ)*(sp4) + (2962282449/50000000000000 : ℝ)*(sp7) + (1703882356714819/100000000000000 : ℝ)*(f.failure) + (906345467501009/25000000000000 : ℝ)*(f.sum) + (1714930857799/2122500000000000000000000000 : ℝ)*base65 + (1607047981892590943/212250000000000000000000000000000 : ℝ)*base67 + (1480261664617840943/212250000000000000000000000000000 : ℝ)*base69 + (1688507216457340943/212250000000000000000000000000000 : ℝ)*base71 + (3939171505103/4245000000000000000000000000 : ℝ)*base73 + (2607709793709340943/212250000000000000000000000000000 : ℝ)*base75 + (31554963697090943/212250000000000000000000000000000 : ℝ)*base77 + (2383527934974340943/212250000000000000000000000000000 : ℝ)*base79 + (18269874977213/4245000000000000000000000000 : ℝ)*base81 + (56381303/5000000000000000000000 : ℝ)*base90 + (56381303/5000000000000000000000 : ℝ)*base92 + (56381303/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2699769293448875860967273/1105468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (9174899/1562500000000 : ℝ)*(base19) + (450114677/20000000000000 : ℝ)*(base23) + (6752703/6250000000000 : ℝ)*(lower2) + (151311063/100000000000000 : ℝ)*(upper3) + (376827/195312500000 : ℝ)*(lower4) + (1316936388797/48828125000 : ℝ)*(major0) + (1316936388797/48828125000 : ℝ)*(major1) + (1316936388797/48828125000 : ℝ)*(major2) + (359369771/1000000000000 : ℝ)*(sp2) + (169497341/20000000000000 : ℝ)*(sp3) + (3669536808714723/100000000000000 : ℝ)*(sp4) + (1834768110760593/50000000000000 : ℝ)*(sp5) + (1834749310582119/50000000000000 : ℝ)*(sp6) + (862316855452301/50000000000000 : ℝ)*(sp7) + (862317279195653/50000000000000 : ℝ)*(f.failure) + (3669536808714723/100000000000000 : ℝ)*(f.sum) + (11532185610857/4245000000000000000000000000 : ℝ)*base65 + (5377026723254773/13265625000000000000000000000000 : ℝ)*base68 + (8691566682739801/6632812500000000000000000000000 : ℝ)*base69 + (34378603132489801/6632812500000000000000000000000 : ℝ)*base71 + (8824945661293/4245000000000000000000000000 : ℝ)*base74 + (49007787425896051/6632812500000000000000000000000 : ℝ)*base75 + (27101136707802301/6632812500000000000000000000000 : ℝ)*base77 + (50645405996651477/13265625000000000000000000000000 : ℝ)*base79 + (583890133633/265312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (35210161/2500000000000000000000 : ℝ)*base90 + (35210161/2500000000000000000000 : ℝ)*base92 + (35210161/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1384_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3831/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1384_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1384_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1384_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1384_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5057/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15947/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
