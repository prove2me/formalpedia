-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:08.273984+00:00
-- url     : https://prove2.me/submissions/993ac0cd-2a8e-4d01-8ae0-81f6eb8b4736

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
theorem support_rectangle_w1125_s6_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108750417/500000000 : ℝ)*x 0 + (1348430937/2500000000 : ℝ)*x 1 + (1316274753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108750417/500000000 : ℝ)^4159 ≤ (528582305527/4000000000000 : ℝ)^3135 := by
    have hnat : (108750417 : ℕ)^4159*4000000000000^3135 ≤ 528582305527^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108750417 500000000 528582305527 4000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348430937/2500000000 : ℝ)^4159 ≤ (22043686751771/50000000000000 : ℝ)^3135 := by
    have hnat : (1348430937 : ℕ)^4159*50000000000000^3135 ≤ 22043686751771^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348430937 2500000000 22043686751771 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316274753/2500000000 : ℝ)^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135 := by
    have hnat : (1316274753 : ℕ)^4159*50000000000000^3135 ≤ 21349034423169^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316274753 2500000000 21349034423169 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108750417/500000000 : ℝ), (1348430937/2500000000 : ℝ), (1316274753/2500000000 : ℝ)] ![(528582305527/4000000000000 : ℝ), (22043686751771/50000000000000 : ℝ), (21349034423169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108750417/500000000 : ℝ)|^4159 ≤ (528582305527/4000000000000 : ℝ)^3135
        have hw : |(-108750417/500000000 : ℝ)|=(108750417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348430937/2500000000 : ℝ)|^4159 ≤ (22043686751771/50000000000000 : ℝ)^3135
        have hw : |(1348430937/2500000000 : ℝ)|=(1348430937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316274753/2500000000 : ℝ)|^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135
        have hw : |(1316274753/2500000000 : ℝ)|=(1316274753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534491451/1000000000 : ℝ)*x 0 + (-2240258811/10000000000 : ℝ)*x 1 + (1316274753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534491451/1000000000 : ℝ)^4159 ≤ (5444860662181/12500000000000 : ℝ)^3135 := by
    have hnat : (534491451 : ℕ)^4159*12500000000000^3135 ≤ 5444860662181^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534491451 1000000000 5444860662181 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240258811/10000000000 : ℝ)^4159 ≤ (13743045836167/100000000000000 : ℝ)^3135 := by
    have hnat : (2240258811 : ℕ)^4159*100000000000000^3135 ≤ 13743045836167^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240258811 10000000000 13743045836167 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316274753/2500000000 : ℝ)^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135 := by
    have hnat : (1316274753 : ℕ)^4159*50000000000000^3135 ≤ 21349034423169^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316274753 2500000000 21349034423169 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534491451/1000000000 : ℝ), (-2240258811/10000000000 : ℝ), (1316274753/2500000000 : ℝ)] ![(5444860662181/12500000000000 : ℝ), (13743045836167/100000000000000 : ℝ), (21349034423169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534491451/1000000000 : ℝ)|^4159 ≤ (5444860662181/12500000000000 : ℝ)^3135
        have hw : |(534491451/1000000000 : ℝ)|=(534491451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2240258811/10000000000 : ℝ)|^4159 ≤ (13743045836167/100000000000000 : ℝ)^3135
        have hw : |(-2240258811/10000000000 : ℝ)|=(2240258811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316274753/2500000000 : ℝ)|^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135
        have hw : |(1316274753/2500000000 : ℝ)|=(1316274753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534491451/1000000000 : ℝ)*x 0 + (1316274753/2500000000 : ℝ)*x 1 + (-2240258811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534491451/1000000000 : ℝ)^4159 ≤ (5444860662181/12500000000000 : ℝ)^3135 := by
    have hnat : (534491451 : ℕ)^4159*12500000000000^3135 ≤ 5444860662181^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534491451 1000000000 5444860662181 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316274753/2500000000 : ℝ)^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135 := by
    have hnat : (1316274753 : ℕ)^4159*50000000000000^3135 ≤ 21349034423169^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316274753 2500000000 21349034423169 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240258811/10000000000 : ℝ)^4159 ≤ (13743045836167/100000000000000 : ℝ)^3135 := by
    have hnat : (2240258811 : ℕ)^4159*100000000000000^3135 ≤ 13743045836167^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240258811 10000000000 13743045836167 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534491451/1000000000 : ℝ), (1316274753/2500000000 : ℝ), (-2240258811/10000000000 : ℝ)] ![(5444860662181/12500000000000 : ℝ), (21349034423169/50000000000000 : ℝ), (13743045836167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534491451/1000000000 : ℝ)|^4159 ≤ (5444860662181/12500000000000 : ℝ)^3135
        have hw : |(534491451/1000000000 : ℝ)|=(534491451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316274753/2500000000 : ℝ)|^4159 ≤ (21349034423169/50000000000000 : ℝ)^3135
        have hw : |(1316274753/2500000000 : ℝ)|=(1316274753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2240258811/10000000000 : ℝ)|^4159 ≤ (13743045836167/100000000000000 : ℝ)^3135
        have hw : |(-2240258811/10000000000 : ℝ)|=(2240258811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183527263/5000000000 : ℝ)*x 0 + (4241393341/10000000000 : ℝ)*x 1 + (2248217967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183527263/5000000000 : ℝ)^4159 ≤ (4164584886893/12500000000000 : ℝ)^3135 := by
    have hnat : (2183527263 : ℕ)^4159*12500000000000^3135 ≤ 4164584886893^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183527263 5000000000 4164584886893 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241393341/10000000000 : ℝ)^4159 ≤ (32050875090981/100000000000000 : ℝ)^3135 := by
    have hnat : (4241393341 : ℕ)^4159*100000000000000^3135 ≤ 32050875090981^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241393341 10000000000 32050875090981 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248217967/5000000000 : ℝ)^4159 ≤ (6926489160207/20000000000000 : ℝ)^3135 := by
    have hnat : (2248217967 : ℕ)^4159*20000000000000^3135 ≤ 6926489160207^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248217967 5000000000 6926489160207 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183527263/5000000000 : ℝ), (4241393341/10000000000 : ℝ), (2248217967/5000000000 : ℝ)] ![(4164584886893/12500000000000 : ℝ), (32050875090981/100000000000000 : ℝ), (6926489160207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183527263/5000000000 : ℝ)|^4159 ≤ (4164584886893/12500000000000 : ℝ)^3135
        have hw : |(2183527263/5000000000 : ℝ)|=(2183527263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241393341/10000000000 : ℝ)|^4159 ≤ (32050875090981/100000000000000 : ℝ)^3135
        have hw : |(4241393341/10000000000 : ℝ)|=(4241393341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248217967/5000000000 : ℝ)|^4159 ≤ (6926489160207/20000000000000 : ℝ)^3135
        have hw : |(2248217967/5000000000 : ℝ)|=(2248217967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10875067/50000000 : ℝ)*x 0 + (1316355949/2500000000 : ℝ)*x 1 + (5393397747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10875067/50000000 : ℝ)^4159 ≤ (2642919684509/20000000000000 : ℝ)^3135 := by
    have hnat : (10875067 : ℕ)^4159*20000000000000^3135 ≤ 2642919684509^3135*50000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10875067 50000000 2642919684509 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316355949/2500000000 : ℝ)^4159 ≤ (42701563080997/100000000000000 : ℝ)^3135 := by
    have hnat : (1316355949 : ℕ)^4159*100000000000000^3135 ≤ 42701563080997^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316355949 2500000000 42701563080997 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393397747/10000000000 : ℝ)^4159 ≤ (44083838486207/100000000000000 : ℝ)^3135 := by
    have hnat : (5393397747 : ℕ)^4159*100000000000000^3135 ≤ 44083838486207^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393397747 10000000000 44083838486207 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10875067/50000000 : ℝ), (1316355949/2500000000 : ℝ), (5393397747/10000000000 : ℝ)] ![(2642919684509/20000000000000 : ℝ), (42701563080997/100000000000000 : ℝ), (44083838486207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10875067/50000000 : ℝ)|^4159 ≤ (2642919684509/20000000000000 : ℝ)^3135
        have hw : |(-10875067/50000000 : ℝ)|=(10875067/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316355949/2500000000 : ℝ)|^4159 ≤ (42701563080997/100000000000000 : ℝ)^3135
        have hw : |(1316355949/2500000000 : ℝ)|=(1316355949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393397747/10000000000 : ℝ)|^4159 ≤ (44083838486207/100000000000000 : ℝ)^3135
        have hw : |(5393397747/10000000000 : ℝ)|=(5393397747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312368261/10000000000 : ℝ)*x 0 + (-263995009/1250000000 : ℝ)*x 1 + (1078679547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312368261/10000000000 : ℝ)^4159 ≤ (21603680393927/50000000000000 : ℝ)^3135 := by
    have hnat : (5312368261 : ℕ)^4159*50000000000000^3135 ≤ 21603680393927^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312368261 10000000000 21603680393927 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263995009/1250000000 : ℝ)^4159 ≤ (1270880084821/10000000000000 : ℝ)^3135 := by
    have hnat : (263995009 : ℕ)^4159*10000000000000^3135 ≤ 1270880084821^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263995009 1250000000 1270880084821 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078679547/2000000000 : ℝ)^4159 ≤ (22041919178043/50000000000000 : ℝ)^3135 := by
    have hnat : (1078679547 : ℕ)^4159*50000000000000^3135 ≤ 22041919178043^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078679547 2000000000 22041919178043 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312368261/10000000000 : ℝ), (-263995009/1250000000 : ℝ), (1078679547/2000000000 : ℝ)] ![(21603680393927/50000000000000 : ℝ), (1270880084821/10000000000000 : ℝ), (22041919178043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312368261/10000000000 : ℝ)|^4159 ≤ (21603680393927/50000000000000 : ℝ)^3135
        have hw : |(5312368261/10000000000 : ℝ)|=(5312368261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263995009/1250000000 : ℝ)|^4159 ≤ (1270880084821/10000000000000 : ℝ)^3135
        have hw : |(-263995009/1250000000 : ℝ)|=(263995009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078679547/2000000000 : ℝ)|^4159 ≤ (22041919178043/50000000000000 : ℝ)^3135
        have hw : |(1078679547/2000000000 : ℝ)|=(1078679547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312368297/10000000000 : ℝ)*x 0 + (5393397659/10000000000 : ℝ)*x 1 + (-1055980063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312368297/10000000000 : ℝ)^4159 ≤ (43207361176293/100000000000000 : ℝ)^3135 := by
    have hnat : (5312368297 : ℕ)^4159*100000000000000^3135 ≤ 43207361176293^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312368297 10000000000 43207361176293 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393397659/10000000000 : ℝ)^4159 ≤ (22041918765991/50000000000000 : ℝ)^3135 := by
    have hnat : (5393397659 : ℕ)^4159*50000000000000^3135 ≤ 22041918765991^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393397659 10000000000 22041918765991 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055980063/5000000000 : ℝ)^4159 ≤ (198575019989/1562500000000 : ℝ)^3135 := by
    have hnat : (1055980063 : ℕ)^4159*1562500000000^3135 ≤ 198575019989^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055980063 5000000000 198575019989 1562500000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312368297/10000000000 : ℝ), (5393397659/10000000000 : ℝ), (-1055980063/5000000000 : ℝ)] ![(43207361176293/100000000000000 : ℝ), (22041918765991/50000000000000 : ℝ), (198575019989/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312368297/10000000000 : ℝ)|^4159 ≤ (43207361176293/100000000000000 : ℝ)^3135
        have hw : |(5312368297/10000000000 : ℝ)|=(5312368297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393397659/10000000000 : ℝ)|^4159 ≤ (22041918765991/50000000000000 : ℝ)^3135
        have hw : |(5393397659/10000000000 : ℝ)|=(5393397659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055980063/5000000000 : ℝ)|^4159 ≤ (198575019989/1562500000000 : ℝ)^3135
        have hw : |(-1055980063/5000000000 : ℝ)|=(1055980063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s6_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367064463/10000000000 : ℝ)*x 0 + (561973979/1250000000 : ℝ)*x 1 + (2121019891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367064463/10000000000 : ℝ)^4159 ≤ (33316779667799/100000000000000 : ℝ)^3135 := by
    have hnat : (4367064463 : ℕ)^4159*100000000000000^3135 ≤ 33316779667799^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367064463 10000000000 33316779667799 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561973979/1250000000 : ℝ)^4159 ≤ (34625864517287/100000000000000 : ℝ)^3135 := by
    have hnat : (561973979 : ℕ)^4159*100000000000000^3135 ≤ 34625864517287^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561973979 1250000000 34625864517287 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121019891/5000000000 : ℝ)^4159 ≤ (4007169474809/12500000000000 : ℝ)^3135 := by
    have hnat : (2121019891 : ℕ)^4159*12500000000000^3135 ≤ 4007169474809^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121019891 5000000000 4007169474809 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367064463/10000000000 : ℝ), (561973979/1250000000 : ℝ), (2121019891/5000000000 : ℝ)] ![(33316779667799/100000000000000 : ℝ), (34625864517287/100000000000000 : ℝ), (4007169474809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367064463/10000000000 : ℝ)|^4159 ≤ (33316779667799/100000000000000 : ℝ)^3135
        have hw : |(4367064463/10000000000 : ℝ)|=(4367064463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561973979/1250000000 : ℝ)|^4159 ≤ (34625864517287/100000000000000 : ℝ)^3135
        have hw : |(561973979/1250000000 : ℝ)|=(561973979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121019891/5000000000 : ℝ)|^4159 ≤ (4007169474809/12500000000000 : ℝ)^3135
        have hw : |(2121019891/5000000000 : ℝ)|=(2121019891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (8317/2048 : ℝ) ≤ (7110936472432863/50000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^8317 ≤ (7110936472432863/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1129 : ℕ)^8317*50000000000000000000^2048 ≤ 7110936472432863^2048*10000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 7110936472432863 50000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (7110936472432863/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/50000 : ℝ) ^ (8317/2048 : ℝ) ≤ (17444798573743249/50000000000000000000 : ℝ) := by
    have hpowers : (7041/50000 : ℝ)^8317 ≤ (17444798573743249/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7041 : ℕ)^8317*50000000000000000000^2048 ≤ 17444798573743249^2048*50000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 50000 17444798573743249 50000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/50000 : ℝ)) (X := (17444798573743249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007110936472432863/25000000000000000000 : ℝ) ≤ (10000700331225363/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (25007110936472432863/25000000000000000000 : ℝ)^2048 ≤ (10000700331225363/10000000000000000 : ℝ)^8317 := by
      have hnat : (25007110936472432863 : ℕ)^2048*10000000000000000^8317 ≤ 10000700331225363^8317*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007110936472432863 25000000000000000000 10000700331225363 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000700331225363/10000000000000000 : ℝ)) (X := (25007110936472432863/25000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126534733440386007/3125000000000000000 : ℝ) ≤ (10001209110011057/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (3126534733440386007/3125000000000000000 : ℝ)^2048 ≤ (10001209110011057/10000000000000000 : ℝ)^8317 := by
      have hnat : (3126534733440386007 : ℕ)^2048*10000000000000000^8317 ≤ 10001209110011057^8317*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126534733440386007 3125000000000000000 10001209110011057 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001209110011057/10000000000000000 : ℝ)) (X := (3126534733440386007/3125000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017444798573743249/25000000000000000000 : ℝ) ≤ (10001717888796751/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (25017444798573743249/25000000000000000000 : ℝ)^2048 ≤ (10001717888796751/10000000000000000 : ℝ)^8317 := by
      have hnat : (25017444798573743249 : ℕ)^2048*10000000000000000^8317 ≤ 10001717888796751^8317*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017444798573743249 25000000000000000000 10001717888796751 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001717888796751/10000000000000000 : ℝ)) (X := (25017444798573743249/25000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7110936472432863/50000000000000000000 : ℝ) ≤ ((872202096868757593/872500000000000000 : ℝ)+2*(254389392847/139600000000000 : ℝ)*(1129/10000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (872202096868757593/872500000000000000 : ℝ)+2*(254389392847/139600000000000 : ℝ)*(1129/10000 : ℝ)=(10000700331225363/10000000000000000 : ℝ) by norm_num, show 1+2*(7110936472432863/50000000000000000000 : ℝ)=(25007110936472432863/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17444798573743249/50000000000000000000 : ℝ)+(7110936472432863/50000000000000000000 : ℝ) ≤ ((872202096868757593/872500000000000000 : ℝ)+(254389392847/139600000000000 : ℝ)*((7041/50000 : ℝ)+(1129/10000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (872202096868757593/872500000000000000 : ℝ)+(254389392847/139600000000000 : ℝ)*((7041/50000 : ℝ)+(1129/10000 : ℝ))=(10001209110011057/10000000000000000 : ℝ) by norm_num, show 1+(17444798573743249/50000000000000000000 : ℝ)+(7110936472432863/50000000000000000000 : ℝ)=(3126534733440386007/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17444798573743249/50000000000000000000 : ℝ) ≤ ((872202096868757593/872500000000000000 : ℝ)+2*(254389392847/139600000000000 : ℝ)*(7041/50000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (872202096868757593/872500000000000000 : ℝ)+2*(254389392847/139600000000000 : ℝ)*(7041/50000 : ℝ)=(10001717888796751/10000000000000000 : ℝ) by norm_num, show 1+2*(17444798573743249/50000000000000000000 : ℝ)=(25017444798573743249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (872202096868757593/872500000000000000 : ℝ)*(X 1 0+X 2 0)+(254389392847/139600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (872202096868757593/872500000000000000 : ℝ)) (alpha := (254389392847/139600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (872202096868757593/872500000000000000 : ℝ)*(X 0 1+X 2 1)+(254389392847/139600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (872202096868757593/872500000000000000 : ℝ)) (alpha := (254389392847/139600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (872202096868757593/872500000000000000 : ℝ)*(X 0 2+X 1 2)+(254389392847/139600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (872202096868757593/872500000000000000 : ℝ)) (alpha := (254389392847/139600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108750417/500000000 : ℝ)*X 0 0+(1348430937/2500000000 : ℝ)*X 0 1+(1316274753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534491451/1000000000 : ℝ)*X 1 0+(-2240258811/10000000000 : ℝ)*X 1 1+(1316274753/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534491451/1000000000 : ℝ)*X 2 0+(1316274753/2500000000 : ℝ)*X 2 1+(-2240258811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183527263/5000000000 : ℝ)*X 0 0+(4241393341/10000000000 : ℝ)*X 0 1+(2248217967/5000000000 : ℝ)*X 0 2+(2183527263/5000000000 : ℝ)*X 1 0+(4241393341/10000000000 : ℝ)*X 1 1+(2248217967/5000000000 : ℝ)*X 1 2+(2183527263/5000000000 : ℝ)*X 2 0+(4241393341/10000000000 : ℝ)*X 2 1+(2248217967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10875067/50000000 : ℝ)*X 0 0+(1316355949/2500000000 : ℝ)*X 0 1+(5393397747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312368261/10000000000 : ℝ)*X 1 0+(-263995009/1250000000 : ℝ)*X 1 1+(1078679547/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312368297/10000000000 : ℝ)*X 2 0+(5393397659/10000000000 : ℝ)*X 2 1+(-1055980063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367064463/10000000000 : ℝ)*X 0 0+(561973979/1250000000 : ℝ)*X 0 1+(2121019891/5000000000 : ℝ)*X 0 2+(4367064463/10000000000 : ℝ)*X 1 0+(561973979/1250000000 : ℝ)*X 1 1+(2121019891/5000000000 : ℝ)*X 1 2+(4367064463/10000000000 : ℝ)*X 2 0+(561973979/1250000000 : ℝ)*X 2 1+(2121019891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66501821701094822478933807/10906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606035197/50000000000000 : ℝ)*(base19) + (1128953103/100000000000000 : ℝ)*(base23) + (44425481/100000000000000 : ℝ)*(lower2) + (154402261/100000000000000 : ℝ)*(upper3) + (46381047/50000000000000 : ℝ)*(upper5) + (5847784546051741/100000000000000 : ℝ)*(major0) + (5847784546051741/100000000000000 : ℝ)*(major1) + (5847784546051741/100000000000000 : ℝ)*(major2) + (7774588608218507/100000000000000 : ℝ)*(sp0) + (7774620093358121/100000000000000 : ℝ)*(sp1) + (1943655044118853/25000000000000 : ℝ)*(sp2) + (490116219894647/12500000000000 : ℝ)*(sp3) + (32697210009/100000000000000 : ℝ)*(sp4) + (445606621/2500000000000 : ℝ)*(sp7) + (61264805990969/1562500000000 : ℝ)*(f.failure) + (1554924261085703/20000000000000 : ℝ)*(f.sum) + (36128514505053/6980000000000000000000000000 : ℝ)*base66 + (1034551191057461837/87250000000000000000000000000000 : ℝ)*base68 + (382301755926211837/87250000000000000000000000000000 : ℝ)*base70 + (702867254454961837/87250000000000000000000000000000 : ℝ)*base72 + (9484509103073/6980000000000000000000000000 : ℝ)*base74 + (1135008521952461837/87250000000000000000000000000000 : ℝ)*base76 + (1112749642227461837/87250000000000000000000000000000 : ℝ)*base78 + (1235125414978538163/87250000000000000000000000000000 : ℝ)*base79 + (23604359815267/6980000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (17253/1250000000000000000 : ℝ)*base89 + (17253/1250000000000000000 : ℝ)*base91 + (17253/1250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (847823455290154329656673/545312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (44849109/10000000000000 : ℝ)*(base19) + (264228891/50000000000000 : ℝ)*(base23) + (6603653/25000000000000 : ℝ)*(upper2) + (5280081/20000000000000 : ℝ)*(upper3) + (77073619/100000000000000 : ℝ)*(upper5) + (18367103168289/312500000000 : ℝ)*(major0) + (18367103168289/312500000000 : ℝ)*(major1) + (18367103168289/312500000000 : ℝ)*(major2) + (532584229/4000000000000 : ℝ)*(sp1) + (4803931773/50000000000000 : ℝ)*(sp2) + (7814092233952663/100000000000000 : ℝ)*(sp4) + (7814078470855847/100000000000000 : ℝ)*(sp5) + (3907041048815667/50000000000000 : ℝ)*(sp6) + (12315167943523/312500000000 : ℝ)*(sp7) + (12315167943523/312500000000 : ℝ)*(f.failure) + (7814092233952663/100000000000000 : ℝ)*(f.sum) + (146615095751/43625000000000000000000000 : ℝ)*base65 + (539487872371187/68164062500000000000000000000 : ℝ)*base68 + (5080287633054617/1090625000000000000000000000000 : ℝ)*base70 + (10366289310817117/1090625000000000000000000000000 : ℝ)*base72 + (948498796261/349000000000000000000000000 : ℝ)*base74 + (1873304803104617/1090625000000000000000000000000 : ℝ)*base76 + (7942550695266371/545312500000000000000000000000 : ℝ)*base78 + (1781620577921129/545312500000000000000000000000 : ℝ)*base79 + (200270916829/174500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1651/250000000000000000 : ℝ)*base89 + (1651/250000000000000000 : ℝ)*base91 + (1651/250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1125_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s7_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087520151/5000000000 : ℝ)*x 0 + (5393371273/10000000000 : ℝ)*x 1 + (5265430323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087520151/5000000000 : ℝ)^4159 ≤ (41296297679/312500000000 : ℝ)^3135 := by
    have hnat : (1087520151 : ℕ)^4159*312500000000^3135 ≤ 41296297679^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087520151 5000000000 41296297679 312500000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393371273/10000000000 : ℝ)^4159 ≤ (22041775708191/50000000000000 : ℝ)^3135 := by
    have hnat : (5393371273 : ℕ)^4159*50000000000000^3135 ≤ 22041775708191^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393371273 10000000000 22041775708191 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265430323/10000000000 : ℝ)^4159 ≤ (10675408325843/25000000000000 : ℝ)^3135 := by
    have hnat : (5265430323 : ℕ)^4159*25000000000000^3135 ≤ 10675408325843^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265430323 10000000000 10675408325843 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087520151/5000000000 : ℝ), (5393371273/10000000000 : ℝ), (5265430323/10000000000 : ℝ)] ![(41296297679/312500000000 : ℝ), (22041775708191/50000000000000 : ℝ), (10675408325843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087520151/5000000000 : ℝ)|^4159 ≤ (41296297679/312500000000 : ℝ)^3135
        have hw : |(-1087520151/5000000000 : ℝ)|=(1087520151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393371273/10000000000 : ℝ)|^4159 ≤ (22041775708191/50000000000000 : ℝ)^3135
        have hw : |(5393371273/10000000000 : ℝ)|=(5393371273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265430323/10000000000 : ℝ)|^4159 ≤ (10675408325843/25000000000000 : ℝ)^3135
        have hw : |(5265430323/10000000000 : ℝ)|=(5265430323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068965119/2000000000 : ℝ)*x 0 + (-223993893/1000000000 : ℝ)*x 1 + (1316357583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068965119/2000000000 : ℝ)^4159 ≤ (21778961996201/50000000000000 : ℝ)^3135 := by
    have hnat : (1068965119 : ℕ)^4159*50000000000000^3135 ≤ 21778961996201^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068965119 2000000000 21778961996201 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223993893/1000000000 : ℝ)^4159 ≤ (13740442594463/100000000000000 : ℝ)^3135 := by
    have hnat : (223993893 : ℕ)^4159*100000000000000^3135 ≤ 13740442594463^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223993893 1000000000 13740442594463 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316357583/2500000000 : ℝ)^4159 ≤ (42701633400201/100000000000000 : ℝ)^3135 := by
    have hnat : (1316357583 : ℕ)^4159*100000000000000^3135 ≤ 42701633400201^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316357583 2500000000 42701633400201 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068965119/2000000000 : ℝ), (-223993893/1000000000 : ℝ), (1316357583/2500000000 : ℝ)] ![(21778961996201/50000000000000 : ℝ), (13740442594463/100000000000000 : ℝ), (42701633400201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068965119/2000000000 : ℝ)|^4159 ≤ (21778961996201/50000000000000 : ℝ)^3135
        have hw : |(1068965119/2000000000 : ℝ)|=(1068965119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223993893/1000000000 : ℝ)|^4159 ≤ (13740442594463/100000000000000 : ℝ)^3135
        have hw : |(-223993893/1000000000 : ℝ)|=(223993893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316357583/2500000000 : ℝ)|^4159 ≤ (42701633400201/100000000000000 : ℝ)^3135
        have hw : |(1316357583/2500000000 : ℝ)|=(1316357583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672412799/5000000000 : ℝ)*x 0 + (2632715167/5000000000 : ℝ)*x 1 + (-2239938923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672412799/5000000000 : ℝ)^4159 ≤ (10889481006209/25000000000000 : ℝ)^3135 := by
    have hnat : (2672412799 : ℕ)^4159*25000000000000^3135 ≤ 10889481006209^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672412799 5000000000 10889481006209 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632715167/5000000000 : ℝ)^4159 ≤ (42701633421719/100000000000000 : ℝ)^3135 := by
    have hnat : (2632715167 : ℕ)^4159*100000000000000^3135 ≤ 42701633421719^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632715167 5000000000 42701633421719 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239938923/10000000000 : ℝ)^4159 ≤ (13740442537497/100000000000000 : ℝ)^3135 := by
    have hnat : (2239938923 : ℕ)^4159*100000000000000^3135 ≤ 13740442537497^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239938923 10000000000 13740442537497 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672412799/5000000000 : ℝ), (2632715167/5000000000 : ℝ), (-2239938923/10000000000 : ℝ)] ![(10889481006209/25000000000000 : ℝ), (42701633421719/100000000000000 : ℝ), (13740442537497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672412799/5000000000 : ℝ)|^4159 ≤ (10889481006209/25000000000000 : ℝ)^3135
        have hw : |(2672412799/5000000000 : ℝ)|=(2672412799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632715167/5000000000 : ℝ)|^4159 ≤ (42701633421719/100000000000000 : ℝ)^3135
        have hw : |(2632715167/5000000000 : ℝ)|=(2632715167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239938923/10000000000 : ℝ)|^4159 ≤ (13740442537497/100000000000000 : ℝ)^3135
        have hw : |(-2239938923/10000000000 : ℝ)|=(2239938923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183535983/5000000000 : ℝ)*x 0 + (4242069017/10000000000 : ℝ)*x 1 + (899151143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183535983/5000000000 : ℝ)^4159 ≤ (16658427802961/50000000000000 : ℝ)^3135 := by
    have hnat : (2183535983 : ℕ)^4159*50000000000000^3135 ≤ 16658427802961^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183535983 5000000000 16658427802961 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242069017/10000000000 : ℝ)^4159 ≤ (32057648893143/100000000000000 : ℝ)^3135 := by
    have hnat : (4242069017 : ℕ)^4159*100000000000000^3135 ≤ 32057648893143^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242069017 10000000000 32057648893143 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899151143/2000000000 : ℝ)^4159 ≤ (17312747745669/50000000000000 : ℝ)^3135 := by
    have hnat : (899151143 : ℕ)^4159*50000000000000^3135 ≤ 17312747745669^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899151143 2000000000 17312747745669 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183535983/5000000000 : ℝ), (4242069017/10000000000 : ℝ), (899151143/2000000000 : ℝ)] ![(16658427802961/50000000000000 : ℝ), (32057648893143/100000000000000 : ℝ), (17312747745669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183535983/5000000000 : ℝ)|^4159 ≤ (16658427802961/50000000000000 : ℝ)^3135
        have hw : |(2183535983/5000000000 : ℝ)|=(2183535983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242069017/10000000000 : ℝ)|^4159 ≤ (32057648893143/100000000000000 : ℝ)^3135
        have hw : |(4242069017/10000000000 : ℝ)|=(4242069017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899151143/2000000000 : ℝ)|^4159 ≤ (17312747745669/50000000000000 : ℝ)^3135
        have hw : |(899151143/2000000000 : ℝ)|=(899151143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087522613/5000000000 : ℝ)*x 0 + (5265751739/10000000000 : ℝ)*x 1 + (2696524351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087522613/5000000000 : ℝ)^4159 ≤ (660742747283/5000000000000 : ℝ)^3135 := by
    have hnat : (1087522613 : ℕ)^4159*5000000000000^3135 ≤ 660742747283^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087522613 5000000000 660742747283 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265751739/10000000000 : ℝ)^4159 ≤ (10676272843409/25000000000000 : ℝ)^3135 := by
    have hnat : (5265751739 : ℕ)^4159*25000000000000^3135 ≤ 10676272843409^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265751739 10000000000 10676272843409 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696524351/5000000000 : ℝ)^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135 := by
    have hnat : (2696524351 : ℕ)^4159*12500000000000^3135 ≤ 5510006708353^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696524351 5000000000 5510006708353 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087522613/5000000000 : ℝ), (5265751739/10000000000 : ℝ), (2696524351/5000000000 : ℝ)] ![(660742747283/5000000000000 : ℝ), (10676272843409/25000000000000 : ℝ), (5510006708353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087522613/5000000000 : ℝ)|^4159 ≤ (660742747283/5000000000000 : ℝ)^3135
        have hw : |(-1087522613/5000000000 : ℝ)|=(1087522613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265751739/10000000000 : ℝ)|^4159 ≤ (10676272843409/25000000000000 : ℝ)^3135
        have hw : |(5265751739/10000000000 : ℝ)|=(5265751739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696524351/5000000000 : ℝ)|^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135
        have hw : |(2696524351/5000000000 : ℝ)|=(2696524351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332028269/625000000 : ℝ)*x 0 + (-2112320557/10000000000 : ℝ)*x 1 + (2696524351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332028269/625000000 : ℝ)^4159 ≤ (8641653522623/20000000000000 : ℝ)^3135 := by
    have hnat : (332028269 : ℕ)^4159*20000000000000^3135 ≤ 8641653522623^3135*625000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332028269 625000000 8641653522623 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112320557/10000000000 : ℝ)^4159 ≤ (12711678707463/100000000000000 : ℝ)^3135 := by
    have hnat : (2112320557 : ℕ)^4159*100000000000000^3135 ≤ 12711678707463^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112320557 10000000000 12711678707463 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696524351/5000000000 : ℝ)^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135 := by
    have hnat : (2696524351 : ℕ)^4159*12500000000000^3135 ≤ 5510006708353^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696524351 5000000000 5510006708353 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332028269/625000000 : ℝ), (-2112320557/10000000000 : ℝ), (2696524351/5000000000 : ℝ)] ![(8641653522623/20000000000000 : ℝ), (12711678707463/100000000000000 : ℝ), (5510006708353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332028269/625000000 : ℝ)|^4159 ≤ (8641653522623/20000000000000 : ℝ)^3135
        have hw : |(332028269/625000000 : ℝ)|=(332028269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112320557/10000000000 : ℝ)|^4159 ≤ (12711678707463/100000000000000 : ℝ)^3135
        have hw : |(-2112320557/10000000000 : ℝ)|=(2112320557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696524351/5000000000 : ℝ)|^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135
        have hw : |(2696524351/5000000000 : ℝ)|=(2696524351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332028269/625000000 : ℝ)*x 0 + (2696524351/5000000000 : ℝ)*x 1 + (-2112320557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332028269/625000000 : ℝ)^4159 ≤ (8641653522623/20000000000000 : ℝ)^3135 := by
    have hnat : (332028269 : ℕ)^4159*20000000000000^3135 ≤ 8641653522623^3135*625000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332028269 625000000 8641653522623 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696524351/5000000000 : ℝ)^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135 := by
    have hnat : (2696524351 : ℕ)^4159*12500000000000^3135 ≤ 5510006708353^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696524351 5000000000 5510006708353 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112320557/10000000000 : ℝ)^4159 ≤ (12711678707463/100000000000000 : ℝ)^3135 := by
    have hnat : (2112320557 : ℕ)^4159*100000000000000^3135 ≤ 12711678707463^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112320557 10000000000 12711678707463 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332028269/625000000 : ℝ), (2696524351/5000000000 : ℝ), (-2112320557/10000000000 : ℝ)] ![(8641653522623/20000000000000 : ℝ), (5510006708353/12500000000000 : ℝ), (12711678707463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332028269/625000000 : ℝ)|^4159 ≤ (8641653522623/20000000000000 : ℝ)^3135
        have hw : |(332028269/625000000 : ℝ)|=(332028269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696524351/5000000000 : ℝ)|^4159 ≤ (5510006708353/12500000000000 : ℝ)^3135
        have hw : |(2696524351/5000000000 : ℝ)|=(2696524351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112320557/10000000000 : ℝ)|^4159 ≤ (12711678707463/100000000000000 : ℝ)^3135
        have hw : |(-2112320557/10000000000 : ℝ)|=(2112320557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s7_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367081743/10000000000 : ℝ)*x 0 + (140472451/312500000 : ℝ)*x 1 + (1060677151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367081743/10000000000 : ℝ)^4159 ≤ (16658477279671/50000000000000 : ℝ)^3135 := by
    have hnat : (4367081743 : ℕ)^4159*50000000000000^3135 ≤ 16658477279671^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367081743 10000000000 16658477279671 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140472451/312500000 : ℝ)^4159 ≤ (8654746050681/25000000000000 : ℝ)^3135 := by
    have hnat : (140472451 : ℕ)^4159*25000000000000^3135 ≤ 8654746050681^3135*312500000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140472451 312500000 8654746050681 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060677151/2500000000 : ℝ)^4159 ≤ (32064061219747/100000000000000 : ℝ)^3135 := by
    have hnat : (1060677151 : ℕ)^4159*100000000000000^3135 ≤ 32064061219747^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060677151 2500000000 32064061219747 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367081743/10000000000 : ℝ), (140472451/312500000 : ℝ), (1060677151/2500000000 : ℝ)] ![(16658477279671/50000000000000 : ℝ), (8654746050681/25000000000000 : ℝ), (32064061219747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367081743/10000000000 : ℝ)|^4159 ≤ (16658477279671/50000000000000 : ℝ)^3135
        have hw : |(4367081743/10000000000 : ℝ)|=(4367081743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140472451/312500000 : ℝ)|^4159 ≤ (8654746050681/25000000000000 : ℝ)^3135
        have hw : |(140472451/312500000 : ℝ)|=(140472451/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060677151/2500000000 : ℝ)|^4159 ≤ (32064061219747/100000000000000 : ℝ)^3135
        have hw : |(1060677151/2500000000 : ℝ)|=(1060677151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11323/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (14391445654841179/100000000000000000000 : ℝ) := by
    have hpowers : (11323/100000 : ℝ)^8317 ≤ (14391445654841179/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11323 : ℕ)^8317*100000000000000000000^2048 ≤ 14391445654841179^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11323 100000 14391445654841179 100000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11323/100000 : ℝ)) (X := (14391445654841179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (34538777404481419/100000000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^8317 ≤ (34538777404481419/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14047 : ℕ)^8317*100000000000000000000^2048 ≤ 34538777404481419^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 34538777404481419 100000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (34538777404481419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014391445654841179/50000000000000000000 : ℝ) ≤ (10000708680630873/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50014391445654841179/50000000000000000000 : ℝ)^2048 ≤ (10000708680630873/10000000000000000 : ℝ)^8317 := by
      have hnat : (50014391445654841179 : ℕ)^2048*10000000000000000^8317 ≤ 10000708680630873^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014391445654841179 50000000000000000000 10000708680630873 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000708680630873/10000000000000000 : ℝ)) (X := (50014391445654841179/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024465111529661299/50000000000000000000 : ℝ) ≤ (10001204648584737/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50024465111529661299/50000000000000000000 : ℝ)^2048 ≤ (10001204648584737/10000000000000000 : ℝ)^8317 := by
      have hnat : (50024465111529661299 : ℕ)^2048*10000000000000000^8317 ≤ 10001204648584737^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024465111529661299 50000000000000000000 10001204648584737 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001204648584737/10000000000000000 : ℝ)) (X := (50024465111529661299/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034538777404481419/50000000000000000000 : ℝ) ≤ (10001700616538601/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50034538777404481419/50000000000000000000 : ℝ)^2048 ≤ (10001700616538601/10000000000000000 : ℝ)^8317 := by
      have hnat : (50034538777404481419 : ℕ)^2048*10000000000000000^8317 ≤ 10001700616538601^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034538777404481419 50000000000000000000 10001700616538601 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001700616538601/10000000000000000 : ℝ)) (X := (50034538777404481419/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14391445654841179/100000000000000000000 : ℝ) ≤ ((2269224896312941159/2270000000000000000 : ℝ)+2*(20665331411/11350000000000 : ℝ)*(11323/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (2269224896312941159/2270000000000000000 : ℝ)+2*(20665331411/11350000000000 : ℝ)*(11323/100000 : ℝ)=(10000708680630873/10000000000000000 : ℝ) by norm_num, show 1+2*(14391445654841179/100000000000000000000 : ℝ)=(50014391445654841179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34538777404481419/100000000000000000000 : ℝ)+(14391445654841179/100000000000000000000 : ℝ) ≤ ((2269224896312941159/2270000000000000000 : ℝ)+(20665331411/11350000000000 : ℝ)*((14047/100000 : ℝ)+(11323/100000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (2269224896312941159/2270000000000000000 : ℝ)+(20665331411/11350000000000 : ℝ)*((14047/100000 : ℝ)+(11323/100000 : ℝ))=(10001204648584737/10000000000000000 : ℝ) by norm_num, show 1+(34538777404481419/100000000000000000000 : ℝ)+(14391445654841179/100000000000000000000 : ℝ)=(50024465111529661299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34538777404481419/100000000000000000000 : ℝ) ≤ ((2269224896312941159/2270000000000000000 : ℝ)+2*(20665331411/11350000000000 : ℝ)*(14047/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (2269224896312941159/2270000000000000000 : ℝ)+2*(20665331411/11350000000000 : ℝ)*(14047/100000 : ℝ)=(10001700616538601/10000000000000000 : ℝ) by norm_num, show 1+2*(34538777404481419/100000000000000000000 : ℝ)=(50034538777404481419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2269224896312941159/2270000000000000000 : ℝ)*(X 1 0+X 2 0)+(20665331411/11350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2269224896312941159/2270000000000000000 : ℝ)) (alpha := (20665331411/11350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2269224896312941159/2270000000000000000 : ℝ)*(X 0 1+X 2 1)+(20665331411/11350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2269224896312941159/2270000000000000000 : ℝ)) (alpha := (20665331411/11350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2269224896312941159/2270000000000000000 : ℝ)*(X 0 2+X 1 2)+(20665331411/11350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (2269224896312941159/2270000000000000000 : ℝ)) (alpha := (20665331411/11350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087520151/5000000000 : ℝ)*X 0 0+(5393371273/10000000000 : ℝ)*X 0 1+(5265430323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068965119/2000000000 : ℝ)*X 1 0+(-223993893/1000000000 : ℝ)*X 1 1+(1316357583/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672412799/5000000000 : ℝ)*X 2 0+(2632715167/5000000000 : ℝ)*X 2 1+(-2239938923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183535983/5000000000 : ℝ)*X 0 0+(4242069017/10000000000 : ℝ)*X 0 1+(899151143/2000000000 : ℝ)*X 0 2+(2183535983/5000000000 : ℝ)*X 1 0+(4242069017/10000000000 : ℝ)*X 1 1+(899151143/2000000000 : ℝ)*X 1 2+(2183535983/5000000000 : ℝ)*X 2 0+(4242069017/10000000000 : ℝ)*X 2 1+(899151143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087522613/5000000000 : ℝ)*X 0 0+(5265751739/10000000000 : ℝ)*X 0 1+(2696524351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332028269/625000000 : ℝ)*X 1 0+(-2112320557/10000000000 : ℝ)*X 1 1+(2696524351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332028269/625000000 : ℝ)*X 2 0+(2696524351/5000000000 : ℝ)*X 2 1+(-2112320557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367081743/10000000000 : ℝ)*X 0 0+(140472451/312500000 : ℝ)*X 0 1+(1060677151/2500000000 : ℝ)*X 0 2+(4367081743/10000000000 : ℝ)*X 1 0+(140472451/312500000 : ℝ)*X 1 1+(1060677151/2500000000 : ℝ)*X 1 2+(4367081743/10000000000 : ℝ)*X 2 0+(140472451/312500000 : ℝ)*X 2 1+(1060677151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3767391921437644269921/567500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1329305381/100000000000000 : ℝ)*(base19) + (250634651/20000000000000 : ℝ)*(base23) + (860723/2000000000000 : ℝ)*(lower2) + (162329271/100000000000000 : ℝ)*(upper3) + (22881343/20000000000000 : ℝ)*(upper5) + (367440262229913/6250000000000 : ℝ)*(major0) + (367440262229913/6250000000000 : ℝ)*(major1) + (367440262229913/6250000000000 : ℝ)*(major2) + (3908071900384551/50000000000000 : ℝ)*(sp0) + (1954044904815643/25000000000000 : ℝ)*(sp1) + (3908089847697349/50000000000000 : ℝ)*(sp2) + (78837757537349/2000000000000 : ℝ)*(sp3) + (37147798851/100000000000000 : ℝ)*(sp4) + (19344635937/100000000000000 : ℝ)*(sp7) + (3941907221503387/100000000000000 : ℝ)*(f.failure) + (7816180948567953/100000000000000 : ℝ)*(f.sum) + (35714248041/1135000000000000000000000000 : ℝ)*base65 + (140472037824601667/14187500000000000000000000000000 : ℝ)*base67 + (35286314055335833/14187500000000000000000000000000 : ℝ)*base70 + (275502469492523333/14187500000000000000000000000000 : ℝ)*base72 + (2878489154393/567500000000000000000000000 : ℝ)*base73 + (218014295306414167/14187500000000000000000000000000 : ℝ)*base75 + (82976653161976667/14187500000000000000000000000000 : ℝ)*base77 + (47423103432835833/14187500000000000000000000000000 : ℝ)*base80 + (1230868168041/283750000000000000000000000 : ℝ)*base82 + (255019/80000000000000000000 : ℝ)*base89 + (255019/80000000000000000000 : ℝ)*base91 + (255019/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1601859103535449536393/283750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040686421/100000000000000 : ℝ)*(base19) + (22622149/2000000000000 : ℝ)*(base23) + (11374497/10000000000000 : ℝ)*(upper3) + (41150563/100000000000000 : ℝ)*(lower4) + (2896357/2500000000000 : ℝ)*(upper5) + (46161939989161/781250000000 : ℝ)*(major0) + (46161939989161/781250000000 : ℝ)*(major1) + (46161939989161/781250000000 : ℝ)*(major2) + (7163823609/25000000000000 : ℝ)*(sp1) + (1231283981/4000000000000 : ℝ)*(sp2) + (1963911495569581/25000000000000 : ℝ)*(sp4) + (7855616286297467/100000000000000 : ℝ)*(sp5) + (7855614069071349/100000000000000 : ℝ)*(sp6) + (792362093353921/20000000000000 : ℝ)*(sp7) + (792362093353921/20000000000000 : ℝ)*(f.failure) + (1963911495569581/25000000000000 : ℝ)*(f.sum) + (4144694829491/1135000000000000000000000000 : ℝ)*base65 + (9158767061678651/1773437500000000000000000000000 : ℝ)*base68 + (11783724251866151/1773437500000000000000000000000 : ℝ)*base70 + (7179672997127073/3546875000000000000000000000000 : ℝ)*base71 + (6296847163959/1135000000000000000000000000 : ℝ)*base74 + (2758491482168487/886718750000000000000000000000 : ℝ)*base75 + (12316698397658323/3546875000000000000000000000000 : ℝ)*base77 + (31196964366553651/1773437500000000000000000000000 : ℝ)*base80 + (424378016689/283750000000000000000000000 : ℝ)*base81 + (39823/16000000000000000000 : ℝ)*base90 + (39823/16000000000000000000 : ℝ)*base92 + (39823/16000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1125_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s8_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175045279/10000000000 : ℝ)*x 0 + (1078659979/2000000000 : ℝ)*x 1 + (658187317/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175045279/10000000000 : ℝ)^4159 ≤ (264297107457/2000000000000 : ℝ)^3135 := by
    have hnat : (2175045279 : ℕ)^4159*2000000000000^3135 ≤ 264297107457^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175045279 10000000000 264297107457 2000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078659979/2000000000 : ℝ)^4159 ≤ (11020694358503/25000000000000 : ℝ)^3135 := by
    have hnat : (1078659979 : ℕ)^4159*25000000000000^3135 ≤ 11020694358503^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078659979 2000000000 11020694358503 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658187317/1250000000 : ℝ)^4159 ≤ (10675591797959/25000000000000 : ℝ)^3135 := by
    have hnat : (658187317 : ℕ)^4159*25000000000000^3135 ≤ 10675591797959^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658187317 1250000000 10675591797959 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175045279/10000000000 : ℝ), (1078659979/2000000000 : ℝ), (658187317/1250000000 : ℝ)] ![(264297107457/2000000000000 : ℝ), (11020694358503/25000000000000 : ℝ), (10675591797959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175045279/10000000000 : ℝ)|^4159 ≤ (264297107457/2000000000000 : ℝ)^3135
        have hw : |(-2175045279/10000000000 : ℝ)|=(2175045279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078659979/2000000000 : ℝ)|^4159 ≤ (11020694358503/25000000000000 : ℝ)^3135
        have hw : |(1078659979/2000000000 : ℝ)|=(1078659979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658187317/1250000000 : ℝ)|^4159 ≤ (10675591797959/25000000000000 : ℝ)^3135
        have hw : |(658187317/1250000000 : ℝ)|=(658187317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344808039/10000000000 : ℝ)*x 0 + (-89594919/400000000 : ℝ)*x 1 + (2632748931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344808039/10000000000 : ℝ)^4159 ≤ (21778867093111/50000000000000 : ℝ)^3135 := by
    have hnat : (5344808039 : ℕ)^4159*50000000000000^3135 ≤ 21778867093111^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344808039 10000000000 21778867093111 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89594919/400000000 : ℝ)^4159 ≤ (13739905857437/100000000000000 : ℝ)^3135 := by
    have hnat : (89594919 : ℕ)^4159*100000000000000^3135 ≤ 13739905857437^3135*400000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89594919 400000000 13739905857437 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632748931/5000000000 : ℝ)^4159 ≤ (8540471988081/20000000000000 : ℝ)^3135 := by
    have hnat : (2632748931 : ℕ)^4159*20000000000000^3135 ≤ 8540471988081^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632748931 5000000000 8540471988081 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344808039/10000000000 : ℝ), (-89594919/400000000 : ℝ), (2632748931/5000000000 : ℝ)] ![(21778867093111/50000000000000 : ℝ), (13739905857437/100000000000000 : ℝ), (8540471988081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344808039/10000000000 : ℝ)|^4159 ≤ (21778867093111/50000000000000 : ℝ)^3135
        have hw : |(5344808039/10000000000 : ℝ)|=(5344808039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89594919/400000000 : ℝ)|^4159 ≤ (13739905857437/100000000000000 : ℝ)^3135
        have hw : |(-89594919/400000000 : ℝ)|=(89594919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632748931/5000000000 : ℝ)|^4159 ≤ (8540471988081/20000000000000 : ℝ)^3135
        have hw : |(2632748931/5000000000 : ℝ)|=(2632748931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336202209/2500000000 : ℝ)*x 0 + (5265497041/10000000000 : ℝ)*x 1 + (-1119936501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336202209/2500000000 : ℝ)^4159 ≤ (544471785037/1250000000000 : ℝ)^3135 := by
    have hnat : (1336202209 : ℕ)^4159*1250000000000^3135 ≤ 544471785037^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336202209 2500000000 544471785037 1250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265497041/10000000000 : ℝ)^4159 ≤ (42702351107431/100000000000000 : ℝ)^3135 := by
    have hnat : (5265497041 : ℕ)^4159*100000000000000^3135 ≤ 42702351107431^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265497041 10000000000 42702351107431 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119936501/5000000000 : ℝ)^4159 ≤ (343497651929/2500000000000 : ℝ)^3135 := by
    have hnat : (1119936501 : ℕ)^4159*2500000000000^3135 ≤ 343497651929^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119936501 5000000000 343497651929 2500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336202209/2500000000 : ℝ), (5265497041/10000000000 : ℝ), (-1119936501/5000000000 : ℝ)] ![(544471785037/1250000000000 : ℝ), (42702351107431/100000000000000 : ℝ), (343497651929/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336202209/2500000000 : ℝ)|^4159 ≤ (544471785037/1250000000000 : ℝ)^3135
        have hw : |(1336202209/2500000000 : ℝ)|=(1336202209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265497041/10000000000 : ℝ)|^4159 ≤ (42702351107431/100000000000000 : ℝ)^3135
        have hw : |(5265497041/10000000000 : ℝ)|=(5265497041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119936501/5000000000 : ℝ)|^4159 ≤ (343497651929/2500000000000 : ℝ)^3135
        have hw : |(-1119936501/5000000000 : ℝ)|=(1119936501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091768867/2500000000 : ℝ)*x 0 + (1060551699/2500000000 : ℝ)*x 1 + (2247808527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091768867/2500000000 : ℝ)^4159 ≤ (166584455249/500000000000 : ℝ)^3135 := by
    have hnat : (1091768867 : ℕ)^4159*500000000000^3135 ≤ 166584455249^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091768867 2500000000 166584455249 500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060551699/2500000000 : ℝ)^4159 ≤ (16029515100759/50000000000000 : ℝ)^3135 := by
    have hnat : (1060551699 : ℕ)^4159*50000000000000^3135 ≤ 16029515100759^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060551699 2500000000 16029515100759 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247808527/5000000000 : ℝ)^4159 ≤ (34624078729639/100000000000000 : ℝ)^3135 := by
    have hnat : (2247808527 : ℕ)^4159*100000000000000^3135 ≤ 34624078729639^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247808527 5000000000 34624078729639 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091768867/2500000000 : ℝ), (1060551699/2500000000 : ℝ), (2247808527/5000000000 : ℝ)] ![(166584455249/500000000000 : ℝ), (16029515100759/50000000000000 : ℝ), (34624078729639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091768867/2500000000 : ℝ)|^4159 ≤ (166584455249/500000000000 : ℝ)^3135
        have hw : |(1091768867/2500000000 : ℝ)|=(1091768867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060551699/2500000000 : ℝ)|^4159 ≤ (16029515100759/50000000000000 : ℝ)^3135
        have hw : |(1060551699/2500000000 : ℝ)|=(1060551699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247808527/5000000000 : ℝ)|^4159 ≤ (34624078729639/100000000000000 : ℝ)^3135
        have hw : |(2247808527/5000000000 : ℝ)|=(2247808527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-543762589/2500000000 : ℝ)*x 0 + (5265818799/10000000000 : ℝ)*x 1 + (107859567/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543762589/2500000000 : ℝ)^4159 ≤ (1321489629447/10000000000000 : ℝ)^3135 := by
    have hnat : (543762589 : ℕ)^4159*10000000000000^3135 ≤ 1321489629447^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543762589 2500000000 1321489629447 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265818799/10000000000 : ℝ)^4159 ≤ (42705812871589/100000000000000 : ℝ)^3135 := by
    have hnat : (5265818799 : ℕ)^4159*100000000000000^3135 ≤ 42705812871589^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265818799 10000000000 42705812871589 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107859567/200000000 : ℝ)^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135 := by
    have hnat : (107859567 : ℕ)^4159*100000000000000^3135 ≤ 44079290824693^3135*200000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107859567 200000000 44079290824693 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543762589/2500000000 : ℝ), (5265818799/10000000000 : ℝ), (107859567/200000000 : ℝ)] ![(1321489629447/10000000000000 : ℝ), (42705812871589/100000000000000 : ℝ), (44079290824693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543762589/2500000000 : ℝ)|^4159 ≤ (1321489629447/10000000000000 : ℝ)^3135
        have hw : |(-543762589/2500000000 : ℝ)|=(543762589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265818799/10000000000 : ℝ)|^4159 ≤ (42705812871589/100000000000000 : ℝ)^3135
        have hw : |(5265818799/10000000000 : ℝ)|=(5265818799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107859567/200000000 : ℝ)|^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135
        have hw : |(107859567/200000000 : ℝ)|=(107859567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664058731/1250000000 : ℝ)*x 0 + (-2112392397/10000000000 : ℝ)*x 1 + (107859567/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664058731/1250000000 : ℝ)^4159 ≤ (5401057114217/12500000000000 : ℝ)^3135 := by
    have hnat : (664058731 : ℕ)^4159*12500000000000^3135 ≤ 5401057114217^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664058731 1250000000 5401057114217 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112392397/10000000000 : ℝ)^4159 ≤ (12712252246777/100000000000000 : ℝ)^3135 := by
    have hnat : (2112392397 : ℕ)^4159*100000000000000^3135 ≤ 12712252246777^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112392397 10000000000 12712252246777 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107859567/200000000 : ℝ)^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135 := by
    have hnat : (107859567 : ℕ)^4159*100000000000000^3135 ≤ 44079290824693^3135*200000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107859567 200000000 44079290824693 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664058731/1250000000 : ℝ), (-2112392397/10000000000 : ℝ), (107859567/200000000 : ℝ)] ![(5401057114217/12500000000000 : ℝ), (12712252246777/100000000000000 : ℝ), (44079290824693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664058731/1250000000 : ℝ)|^4159 ≤ (5401057114217/12500000000000 : ℝ)^3135
        have hw : |(664058731/1250000000 : ℝ)|=(664058731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112392397/10000000000 : ℝ)|^4159 ≤ (12712252246777/100000000000000 : ℝ)^3135
        have hw : |(-2112392397/10000000000 : ℝ)|=(2112392397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107859567/200000000 : ℝ)|^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135
        have hw : |(107859567/200000000 : ℝ)|=(107859567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664058731/1250000000 : ℝ)*x 0 + (107859567/200000000 : ℝ)*x 1 + (-2112392397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664058731/1250000000 : ℝ)^4159 ≤ (5401057114217/12500000000000 : ℝ)^3135 := by
    have hnat : (664058731 : ℕ)^4159*12500000000000^3135 ≤ 5401057114217^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664058731 1250000000 5401057114217 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107859567/200000000 : ℝ)^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135 := by
    have hnat : (107859567 : ℕ)^4159*100000000000000^3135 ≤ 44079290824693^3135*200000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107859567 200000000 44079290824693 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112392397/10000000000 : ℝ)^4159 ≤ (12712252246777/100000000000000 : ℝ)^3135 := by
    have hnat : (2112392397 : ℕ)^4159*100000000000000^3135 ≤ 12712252246777^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112392397 10000000000 12712252246777 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664058731/1250000000 : ℝ), (107859567/200000000 : ℝ), (-2112392397/10000000000 : ℝ)] ![(5401057114217/12500000000000 : ℝ), (44079290824693/100000000000000 : ℝ), (12712252246777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664058731/1250000000 : ℝ)|^4159 ≤ (5401057114217/12500000000000 : ℝ)^3135
        have hw : |(664058731/1250000000 : ℝ)|=(664058731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107859567/200000000 : ℝ)|^4159 ≤ (44079290824693/100000000000000 : ℝ)^3135
        have hw : |(107859567/200000000 : ℝ)|=(107859567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112392397/10000000000 : ℝ)|^4159 ≤ (12712252246777/100000000000000 : ℝ)^3135
        have hw : |(-2112392397/10000000000 : ℝ)|=(2112392397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s8_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367085239/10000000000 : ℝ)*x 0 + (561872717/1250000000 : ℝ)*x 1 + (2121422187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367085239/10000000000 : ℝ)^4159 ≤ (33316989942519/100000000000000 : ℝ)^3135 := by
    have hnat : (4367085239 : ℕ)^4159*100000000000000^3135 ≤ 33316989942519^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367085239 10000000000 33316989942519 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561872717/1250000000 : ℝ)^4159 ≤ (6923517516577/20000000000000 : ℝ)^3135 := by
    have hnat : (561872717 : ℕ)^4159*20000000000000^3135 ≤ 6923517516577^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561872717 1250000000 6923517516577 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121422187/5000000000 : ℝ)^4159 ≤ (2004088903359/6250000000000 : ℝ)^3135 := by
    have hnat : (2121422187 : ℕ)^4159*6250000000000^3135 ≤ 2004088903359^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121422187 5000000000 2004088903359 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367085239/10000000000 : ℝ), (561872717/1250000000 : ℝ), (2121422187/5000000000 : ℝ)] ![(33316989942519/100000000000000 : ℝ), (6923517516577/20000000000000 : ℝ), (2004088903359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367085239/10000000000 : ℝ)|^4159 ≤ (33316989942519/100000000000000 : ℝ)^3135
        have hw : |(4367085239/10000000000 : ℝ)|=(4367085239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561872717/1250000000 : ℝ)|^4159 ≤ (6923517516577/20000000000000 : ℝ)^3135
        have hw : |(561872717/1250000000 : ℝ)|=(561872717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121422187/5000000000 : ℝ)|^4159 ≤ (2004088903359/6250000000000 : ℝ)^3135
        have hw : |(2121422187/5000000000 : ℝ)|=(2121422187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1133/10000 : ℝ) ^ (8317/2048 : ℝ) ≤ (1442761066619779/10000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^8317 ≤ (1442761066619779/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1133 : ℕ)^8317*10000000000000000000^2048 ≤ 1442761066619779^2048*10000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 1442761066619779 10000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (1442761066619779/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (8317/2048 : ℝ) ≤ (3446893375587887/10000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^8317 ≤ (3446893375587887/10000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8317*10000000000000000000^2048 ≤ 3446893375587887^2048*2500^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 3446893375587887 10000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (3446893375587887/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001442761066619779/5000000000000000000 : ℝ) ≤ (5000355230658809/5000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (5001442761066619779/5000000000000000000 : ℝ)^2048 ≤ (5000355230658809/5000000000000000 : ℝ)^8317 := by
      have hnat : (5001442761066619779 : ℕ)^2048*5000000000000000^8317 ≤ 5000355230658809^8317*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001442761066619779 5000000000000000000 5000355230658809 5000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000355230658809/5000000000000000 : ℝ)) (X := (5001442761066619779/5000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002444827221103833/5000000000000000000 : ℝ) ≤ (10001203819578723/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (5002444827221103833/5000000000000000000 : ℝ)^2048 ≤ (10001203819578723/10000000000000000 : ℝ)^8317 := by
      have hnat : (5002444827221103833 : ℕ)^2048*10000000000000000^8317 ≤ 10001203819578723^8317*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002444827221103833 5000000000000000000 10001203819578723 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001203819578723/10000000000000000 : ℝ)) (X := (5002444827221103833/5000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003446893375587887/5000000000000000000 : ℝ) ≤ (2500424294459957/2500000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (5003446893375587887/5000000000000000000 : ℝ)^2048 ≤ (2500424294459957/2500000000000000 : ℝ)^8317 := by
      have hnat : (5003446893375587887 : ℕ)^2048*2500000000000000^8317 ≤ 2500424294459957^8317*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003446893375587887 5000000000000000000 2500424294459957 2500000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500424294459957/2500000000000000 : ℝ)) (X := (5003446893375587887/5000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1442761066619779/10000000000000000000 : ℝ) ≤ ((677268646299352637/677500000000000000 : ℝ)+2*(98671652221/54200000000000 : ℝ)*(1133/10000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (677268646299352637/677500000000000000 : ℝ)+2*(98671652221/54200000000000 : ℝ)*(1133/10000 : ℝ)=(5000355230658809/5000000000000000 : ℝ) by norm_num, show 1+2*(1442761066619779/10000000000000000000 : ℝ)=(5001442761066619779/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3446893375587887/10000000000000000000 : ℝ)+(1442761066619779/10000000000000000000 : ℝ) ≤ ((677268646299352637/677500000000000000 : ℝ)+(98671652221/54200000000000 : ℝ)*((351/2500 : ℝ)+(1133/10000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (677268646299352637/677500000000000000 : ℝ)+(98671652221/54200000000000 : ℝ)*((351/2500 : ℝ)+(1133/10000 : ℝ))=(10001203819578723/10000000000000000 : ℝ) by norm_num, show 1+(3446893375587887/10000000000000000000 : ℝ)+(1442761066619779/10000000000000000000 : ℝ)=(5002444827221103833/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3446893375587887/10000000000000000000 : ℝ) ≤ ((677268646299352637/677500000000000000 : ℝ)+2*(98671652221/54200000000000 : ℝ)*(351/2500 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (677268646299352637/677500000000000000 : ℝ)+2*(98671652221/54200000000000 : ℝ)*(351/2500 : ℝ)=(2500424294459957/2500000000000000 : ℝ) by norm_num, show 1+2*(3446893375587887/10000000000000000000 : ℝ)=(5003446893375587887/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (677268646299352637/677500000000000000 : ℝ)*(X 1 0+X 2 0)+(98671652221/54200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (677268646299352637/677500000000000000 : ℝ)) (alpha := (98671652221/54200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (677268646299352637/677500000000000000 : ℝ)*(X 0 1+X 2 1)+(98671652221/54200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (677268646299352637/677500000000000000 : ℝ)) (alpha := (98671652221/54200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (677268646299352637/677500000000000000 : ℝ)*(X 0 2+X 1 2)+(98671652221/54200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (677268646299352637/677500000000000000 : ℝ)) (alpha := (98671652221/54200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2175045279/10000000000 : ℝ)*X 0 0+(1078659979/2000000000 : ℝ)*X 0 1+(658187317/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344808039/10000000000 : ℝ)*X 1 0+(-89594919/400000000 : ℝ)*X 1 1+(2632748931/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336202209/2500000000 : ℝ)*X 2 0+(5265497041/10000000000 : ℝ)*X 2 1+(-1119936501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091768867/2500000000 : ℝ)*X 0 0+(1060551699/2500000000 : ℝ)*X 0 1+(2247808527/5000000000 : ℝ)*X 0 2+(1091768867/2500000000 : ℝ)*X 1 0+(1060551699/2500000000 : ℝ)*X 1 1+(2247808527/5000000000 : ℝ)*X 1 2+(1091768867/2500000000 : ℝ)*X 2 0+(1060551699/2500000000 : ℝ)*X 2 1+(2247808527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543762589/2500000000 : ℝ)*X 0 0+(5265818799/10000000000 : ℝ)*X 0 1+(107859567/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664058731/1250000000 : ℝ)*X 1 0+(-2112392397/10000000000 : ℝ)*X 1 1+(107859567/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664058731/1250000000 : ℝ)*X 2 0+(107859567/200000000 : ℝ)*X 2 1+(-2112392397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367085239/10000000000 : ℝ)*X 0 0+(561872717/1250000000 : ℝ)*X 0 1+(2121422187/5000000000 : ℝ)*X 0 2+(4367085239/10000000000 : ℝ)*X 1 0+(561872717/1250000000 : ℝ)*X 1 1+(2121422187/5000000000 : ℝ)*X 1 2+(4367085239/10000000000 : ℝ)*X 2 0+(561872717/1250000000 : ℝ)*X 2 1+(2121422187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25928780490409746945777/2710000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2026607883/100000000000000 : ℝ)*(base19) + (710941681/25000000000000 : ℝ)*(base23) + (46717597/25000000000000 : ℝ)*(lower2) + (1019187/625000000000 : ℝ)*(upper3) + (78795527/100000000000000 : ℝ)*(upper5) + (5885430650085291/100000000000000 : ℝ)*(major0) + (5885430650085291/100000000000000 : ℝ)*(major1) + (5885430650085291/100000000000000 : ℝ)*(major2) + (7824650528352259/100000000000000 : ℝ)*(sp0) + (3912334803333023/50000000000000 : ℝ)*(sp1) + (3912334394753603/50000000000000 : ℝ)*(sp2) + (3946174863486919/100000000000000 : ℝ)*(sp3) + (2110492167/10000000000000 : ℝ)*(sp4) + (14484482537/100000000000000 : ℝ)*(sp7) + (246636834248091/6250000000000 : ℝ)*(f.failure) + (782467163327393/10000000000000 : ℝ)*(f.sum) + (2715860768971/2710000000000000000000000000 : ℝ)*base65 + (380677908536899867/67750000000000000000000000000000 : ℝ)*base67 + (1177139703984850133/67750000000000000000000000000000 : ℝ)*base70 + (383802176887399867/67750000000000000000000000000000 : ℝ)*base71 + (14796468853949/2710000000000000000000000000 : ℝ)*base74 + (170940845206850133/67750000000000000000000000000000 : ℝ)*base76 + (162623823703100133/67750000000000000000000000000000 : ℝ)*base78 + (330204814966649867/67750000000000000000000000000000 : ℝ)*base79 + (4740403130391/2710000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1467/5000000000000000000 : ℝ)*base89 + (1467/5000000000000000000 : ℝ)*base91 + (1467/5000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174620099170644749952105291/16937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1888557529/100000000000000 : ℝ)*(base19) + (2054470387/100000000000000 : ℝ)*(base23) + (331780259/50000000000000 : ℝ)*(lower1) + (41300403/20000000000000 : ℝ)*(upper3) + (75485073/100000000000000 : ℝ)*(lower4) + (210170923/100000000000000 : ℝ)*(upper5) + (2957536847419581/50000000000000 : ℝ)*(major0) + (2957536847419581/50000000000000 : ℝ)*(major1) + (2957536847419581/50000000000000 : ℝ)*(major2) + (3913426723/100000000000000 : ℝ)*(sp2) + (3932040997881561/50000000000000 : ℝ)*(sp4) + (3932040053602797/50000000000000 : ℝ)*(sp5) + (7864076027866011/100000000000000 : ℝ)*(sp6) + (495758131282423/12500000000000 : ℝ)*(sp7) + (495758131282423/12500000000000 : ℝ)*(f.failure) + (3932040997881561/50000000000000 : ℝ)*(f.sum) + (5098564581719/1355000000000000000000000000 : ℝ)*base66 + (483817891369952403/33875000000000000000000000000000 : ℝ)*base68 + (28528841005797597/33875000000000000000000000000000 : ℝ)*base69 + (2898509915820702403/33875000000000000000000000000000 : ℝ)*base72 + (6457850392271/1355000000000000000000000000 : ℝ)*base73 + (3317185709644202403/33875000000000000000000000000000 : ℝ)*base76 + (313458904936202403/33875000000000000000000000000000 : ℝ)*base78 + (262375255871922597/33875000000000000000000000000000 : ℝ)*base79 + (932600472667/169375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (130951/10000000000000000000 : ℝ)*base89 + (130951/10000000000000000000 : ℝ)*base91 + (130951/10000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1125_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1125_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1125_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1125_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1125_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
