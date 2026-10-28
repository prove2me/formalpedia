-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:59:39.667546+00:00
-- url     : https://prove2.me/submissions/3eb0f461-011e-4a9e-8176-8f40bdae0f6c

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
theorem support_rectangle_w1056_s6_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104324497/5000000000 : ℝ)*x 0 + (5395127087/10000000000 : ℝ)*x 1 + (5263706411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104324497/5000000000 : ℝ)^8249 ≤ (6706283111193/50000000000000 : ℝ)^6201 := by
    have hnat : (1104324497 : ℕ)^8249*50000000000000^6201 ≤ 6706283111193^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104324497 5000000000 6706283111193 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395127087/10000000000 : ℝ)^8249 ≤ (44003787475463/100000000000000 : ℝ)^6201 := by
    have hnat : (5395127087 : ℕ)^8249*100000000000000^6201 ≤ 44003787475463^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395127087 10000000000 44003787475463 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263706411/10000000000 : ℝ)^8249 ≤ (42583646292029/100000000000000 : ℝ)^6201 := by
    have hnat : (5263706411 : ℕ)^8249*100000000000000^6201 ≤ 42583646292029^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263706411 10000000000 42583646292029 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104324497/5000000000 : ℝ), (5395127087/10000000000 : ℝ), (5263706411/10000000000 : ℝ)] ![(6706283111193/50000000000000 : ℝ), (44003787475463/100000000000000 : ℝ), (42583646292029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104324497/5000000000 : ℝ)|^8249 ≤ (6706283111193/50000000000000 : ℝ)^6201
        have hw : |(-1104324497/5000000000 : ℝ)|=(1104324497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395127087/10000000000 : ℝ)|^8249 ≤ (44003787475463/100000000000000 : ℝ)^6201
        have hw : |(5395127087/10000000000 : ℝ)|=(5395127087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263706411/10000000000 : ℝ)|^8249 ≤ (42583646292029/100000000000000 : ℝ)^6201
        have hw : |(5263706411/10000000000 : ℝ)|=(5263706411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334071887/625000000 : ℝ)*x 0 + (-1137669473/5000000000 : ℝ)*x 1 + (5263706419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334071887/625000000 : ℝ)^8249 ≤ (5432796449013/12500000000000 : ℝ)^6201 := by
    have hnat : (334071887 : ℕ)^8249*12500000000000^6201 ≤ 5432796449013^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334071887 625000000 5432796449013 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137669473/5000000000 : ℝ)^8249 ≤ (6976991007169/50000000000000 : ℝ)^6201 := by
    have hnat : (1137669473 : ℕ)^8249*50000000000000^6201 ≤ 6976991007169^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137669473 5000000000 6976991007169 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263706419/10000000000 : ℝ)^8249 ≤ (10645911594531/25000000000000 : ℝ)^6201 := by
    have hnat : (5263706419 : ℕ)^8249*25000000000000^6201 ≤ 10645911594531^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263706419 10000000000 10645911594531 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334071887/625000000 : ℝ), (-1137669473/5000000000 : ℝ), (5263706419/10000000000 : ℝ)] ![(5432796449013/12500000000000 : ℝ), (6976991007169/50000000000000 : ℝ), (10645911594531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334071887/625000000 : ℝ)|^8249 ≤ (5432796449013/12500000000000 : ℝ)^6201
        have hw : |(334071887/625000000 : ℝ)|=(334071887/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137669473/5000000000 : ℝ)|^8249 ≤ (6976991007169/50000000000000 : ℝ)^6201
        have hw : |(-1137669473/5000000000 : ℝ)|=(1137669473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263706419/10000000000 : ℝ)|^8249 ≤ (10645911594531/25000000000000 : ℝ)^6201
        have hw : |(5263706419/10000000000 : ℝ)|=(5263706419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672575003/5000000000 : ℝ)*x 0 + (5263706537/10000000000 : ℝ)*x 1 + (-2275339037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672575003/5000000000 : ℝ)^8249 ≤ (8692473916041/20000000000000 : ℝ)^6201 := by
    have hnat : (2672575003 : ℕ)^8249*20000000000000^6201 ≤ 8692473916041^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672575003 5000000000 8692473916041 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263706537/10000000000 : ℝ)^8249 ≤ (21291823824017/50000000000000 : ℝ)^6201 := by
    have hnat : (5263706537 : ℕ)^8249*50000000000000^6201 ≤ 21291823824017^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263706537 10000000000 21291823824017 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275339037/10000000000 : ℝ)^8249 ≤ (13953982756729/100000000000000 : ℝ)^6201 := by
    have hnat : (2275339037 : ℕ)^8249*100000000000000^6201 ≤ 13953982756729^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275339037 10000000000 13953982756729 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672575003/5000000000 : ℝ), (5263706537/10000000000 : ℝ), (-2275339037/10000000000 : ℝ)] ![(8692473916041/20000000000000 : ℝ), (21291823824017/50000000000000 : ℝ), (13953982756729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672575003/5000000000 : ℝ)|^8249 ≤ (8692473916041/20000000000000 : ℝ)^6201
        have hw : |(2672575003/5000000000 : ℝ)|=(2672575003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263706537/10000000000 : ℝ)|^8249 ≤ (21291823824017/50000000000000 : ℝ)^6201
        have hw : |(5263706537/10000000000 : ℝ)|=(5263706537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2275339037/10000000000 : ℝ)|^8249 ≤ (13953982756729/100000000000000 : ℝ)^6201
        have hw : |(-2275339037/10000000000 : ℝ)|=(2275339037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875380541/2000000000 : ℝ)*x 0 + (2125145717/5000000000 : ℝ)*x 1 + (901469319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875380541/2000000000 : ℝ)^8249 ≤ (33316189944757/100000000000000 : ℝ)^6201 := by
    have hnat : (875380541 : ℕ)^8249*100000000000000^6201 ≤ 33316189944757^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875380541 2000000000 33316189944757 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125145717/5000000000 : ℝ)^8249 ≤ (3204031764007/10000000000000 : ℝ)^6201 := by
    have hnat : (2125145717 : ℕ)^8249*10000000000000^6201 ≤ 3204031764007^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125145717 5000000000 3204031764007 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901469319/2000000000 : ℝ)^8249 ≤ (34643492403313/100000000000000 : ℝ)^6201 := by
    have hnat : (901469319 : ℕ)^8249*100000000000000^6201 ≤ 34643492403313^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901469319 2000000000 34643492403313 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875380541/2000000000 : ℝ), (2125145717/5000000000 : ℝ), (901469319/2000000000 : ℝ)] ![(33316189944757/100000000000000 : ℝ), (3204031764007/10000000000000 : ℝ), (34643492403313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875380541/2000000000 : ℝ)|^8249 ≤ (33316189944757/100000000000000 : ℝ)^6201
        have hw : |(875380541/2000000000 : ℝ)|=(875380541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125145717/5000000000 : ℝ)|^8249 ≤ (3204031764007/10000000000000 : ℝ)^6201
        have hw : |(2125145717/5000000000 : ℝ)|=(2125145717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901469319/2000000000 : ℝ)|^8249 ≤ (34643492403313/100000000000000 : ℝ)^6201
        have hw : |(901469319/2000000000 : ℝ)|=(901469319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104327117/5000000000 : ℝ)*x 0 + (210561537/400000000 : ℝ)*x 1 + (5394793857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104327117/5000000000 : ℝ)^8249 ≤ (335315213829/2500000000000 : ℝ)^6201 := by
    have hnat : (1104327117 : ℕ)^8249*2500000000000^6201 ≤ 335315213829^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104327117 5000000000 335315213829 2500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210561537/400000000 : ℝ)^8249 ≤ (21293609722793/50000000000000 : ℝ)^6201 := by
    have hnat : (210561537 : ℕ)^8249*50000000000000^6201 ≤ 21293609722793^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210561537 400000000 21293609722793 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394793857/10000000000 : ℝ)^8249 ≤ (8800034396343/20000000000000 : ℝ)^6201 := by
    have hnat : (5394793857 : ℕ)^8249*20000000000000^6201 ≤ 8800034396343^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394793857 10000000000 8800034396343 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104327117/5000000000 : ℝ), (210561537/400000000 : ℝ), (5394793857/10000000000 : ℝ)] ![(335315213829/2500000000000 : ℝ), (21293609722793/50000000000000 : ℝ), (8800034396343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104327117/5000000000 : ℝ)|^8249 ≤ (335315213829/2500000000000 : ℝ)^6201
        have hw : |(-1104327117/5000000000 : ℝ)|=(1104327117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210561537/400000000 : ℝ)|^8249 ≤ (21293609722793/50000000000000 : ℝ)^6201
        have hw : |(210561537/400000000 : ℝ)|=(210561537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394793857/10000000000 : ℝ)|^8249 ≤ (8800034396343/20000000000000 : ℝ)^6201
        have hw : |(5394793857/10000000000 : ℝ)|=(5394793857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312074307/10000000000 : ℝ)*x 0 + (-2144251493/10000000000 : ℝ)*x 1 + (5394793981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312074307/10000000000 : ℝ)^8249 ≤ (21552483583791/50000000000000 : ℝ)^6201 := by
    have hnat : (5312074307 : ℕ)^8249*50000000000000^6201 ≤ 21552483583791^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312074307 10000000000 21552483583791 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144251493/10000000000 : ℝ)^8249 ≤ (6447429743121/50000000000000 : ℝ)^6201 := by
    have hnat : (2144251493 : ℕ)^8249*50000000000000^6201 ≤ 6447429743121^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144251493 10000000000 6447429743121 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394793981/10000000000 : ℝ)^8249 ≤ (22000086663541/50000000000000 : ℝ)^6201 := by
    have hnat : (5394793981 : ℕ)^8249*50000000000000^6201 ≤ 22000086663541^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394793981 10000000000 22000086663541 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312074307/10000000000 : ℝ), (-2144251493/10000000000 : ℝ), (5394793981/10000000000 : ℝ)] ![(21552483583791/50000000000000 : ℝ), (6447429743121/50000000000000 : ℝ), (22000086663541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312074307/10000000000 : ℝ)|^8249 ≤ (21552483583791/50000000000000 : ℝ)^6201
        have hw : |(5312074307/10000000000 : ℝ)|=(5312074307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144251493/10000000000 : ℝ)|^8249 ≤ (6447429743121/50000000000000 : ℝ)^6201
        have hw : |(-2144251493/10000000000 : ℝ)|=(2144251493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394793981/10000000000 : ℝ)|^8249 ≤ (22000086663541/50000000000000 : ℝ)^6201
        have hw : |(5394793981/10000000000 : ℝ)|=(5394793981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83001159/156250000 : ℝ)*x 0 + (43158353/80000000 : ℝ)*x 1 + (-85770059/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83001159/156250000 : ℝ)^8249 ≤ (21552482876751/50000000000000 : ℝ)^6201 := by
    have hnat : (83001159 : ℕ)^8249*50000000000000^6201 ≤ 21552482876751^6201*156250000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83001159 156250000 21552482876751 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43158353/80000000 : ℝ)^8249 ≤ (11000043722361/25000000000000 : ℝ)^6201 := by
    have hnat : (43158353 : ℕ)^8249*25000000000000^6201 ≤ 11000043722361^6201*80000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43158353 80000000 11000043722361 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85770059/400000000 : ℝ)^8249 ≤ (2578971868449/20000000000000 : ℝ)^6201 := by
    have hnat : (85770059 : ℕ)^8249*20000000000000^6201 ≤ 2578971868449^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85770059 400000000 2578971868449 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83001159/156250000 : ℝ), (43158353/80000000 : ℝ), (-85770059/400000000 : ℝ)] ![(21552482876751/50000000000000 : ℝ), (11000043722361/25000000000000 : ℝ), (2578971868449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83001159/156250000 : ℝ)|^8249 ≤ (21552482876751/50000000000000 : ℝ)^6201
        have hw : |(83001159/156250000 : ℝ)|=(83001159/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43158353/80000000 : ℝ)|^8249 ≤ (11000043722361/25000000000000 : ℝ)^6201
        have hw : |(43158353/80000000 : ℝ)|=(43158353/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85770059/400000000 : ℝ)|^8249 ≤ (2578971868449/20000000000000 : ℝ)^6201
        have hw : |(-85770059/400000000 : ℝ)|=(85770059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s6_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094228273/2500000000 : ℝ)*x 0 + (901339409/2000000000 : ℝ)*x 1 + (4250943183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094228273/2500000000 : ℝ)^8249 ≤ (33316295121159/100000000000000 : ℝ)^6201 := by
    have hnat : (1094228273 : ℕ)^8249*100000000000000^6201 ≤ 33316295121159^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094228273 2500000000 33316295121159 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901339409/2000000000 : ℝ)^8249 ≤ (17318425632419/50000000000000 : ℝ)^6201 := by
    have hnat : (901339409 : ℕ)^8249*50000000000000^6201 ≤ 17318425632419^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901339409 2000000000 17318425632419 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250943183/10000000000 : ℝ)^8249 ≤ (32046853594953/100000000000000 : ℝ)^6201 := by
    have hnat : (4250943183 : ℕ)^8249*100000000000000^6201 ≤ 32046853594953^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250943183 10000000000 32046853594953 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094228273/2500000000 : ℝ), (901339409/2000000000 : ℝ), (4250943183/10000000000 : ℝ)] ![(33316295121159/100000000000000 : ℝ), (17318425632419/50000000000000 : ℝ), (32046853594953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094228273/2500000000 : ℝ)|^8249 ≤ (33316295121159/100000000000000 : ℝ)^6201
        have hw : |(1094228273/2500000000 : ℝ)|=(1094228273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901339409/2000000000 : ℝ)|^8249 ≤ (17318425632419/50000000000000 : ℝ)^6201
        have hw : |(901339409/2000000000 : ℝ)|=(901339409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250943183/10000000000 : ℝ)|^8249 ≤ (32046853594953/100000000000000 : ℝ)^6201
        have hw : |(4250943183/10000000000 : ℝ)|=(4250943183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5591/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (7362594986704589/50000000000000000000 : ℝ) := by
    have hpowers : (5591/50000 : ℝ)^1031 ≤ (7362594986704589/50000000000000000000 : ℝ)^256 := by
      have hnat : (5591 : ℕ)^1031*50000000000000000000^256 ≤ 7362594986704589^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5591 50000 7362594986704589 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5591/50000 : ℝ)) (X := (7362594986704589/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2811/20000 : ℝ) ^ (1031/256 : ℝ) ≤ (36984682907293253/100000000000000000000 : ℝ) := by
    have hpowers : (2811/20000 : ℝ)^1031 ≤ (36984682907293253/100000000000000000000 : ℝ)^256 := by
      have hnat : (2811 : ℕ)^1031*100000000000000000000^256 ≤ 36984682907293253^256*20000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 20000 36984682907293253 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/20000 : ℝ)) (X := (36984682907293253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007362594986704589/25000000000000000000 : ℝ) ≤ (5000365589859049/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25007362594986704589/25000000000000000000 : ℝ)^256 ≤ (5000365589859049/5000000000000000 : ℝ)^1031 := by
      have hnat : (25007362594986704589 : ℕ)^256*5000000000000000^1031 ≤ 5000365589859049^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007362594986704589 25000000000000000000 5000365589859049 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000365589859049/5000000000000000 : ℝ)) (X := (25007362594986704589/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051709872880702431/100000000000000000000 : ℝ) ≤ (625080232513761/625000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (100051709872880702431/100000000000000000000 : ℝ)^256 ≤ (625080232513761/625000000000000 : ℝ)^1031 := by
      have hnat : (100051709872880702431 : ℕ)^256*625000000000000^1031 ≤ 625080232513761^1031*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051709872880702431 100000000000000000000 625080232513761 625000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625080232513761/625000000000000 : ℝ)) (X := (100051709872880702431/100000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036984682907293253/50000000000000000000 : ℝ) ≤ (5000918130361127/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50036984682907293253/50000000000000000000 : ℝ)^256 ≤ (5000918130361127/5000000000000000 : ℝ)^1031 := by
      have hnat : (50036984682907293253 : ℕ)^256*5000000000000000^1031 ≤ 5000918130361127^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036984682907293253 50000000000000000000 5000918130361127 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000918130361127/5000000000000000 : ℝ)) (X := (50036984682907293253/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7362594986704589/50000000000000000000 : ℝ) ≤ ((14359871831770811581/14365000000000000000 : ℝ)+2*(276270251039/143650000000000 : ℝ)*(5591/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (14359871831770811581/14365000000000000000 : ℝ)+2*(276270251039/143650000000000 : ℝ)*(5591/50000 : ℝ)=(5000365589859049/5000000000000000 : ℝ) by norm_num, show 1+2*(7362594986704589/50000000000000000000 : ℝ)=(25007362594986704589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36984682907293253/100000000000000000000 : ℝ)+(7362594986704589/50000000000000000000 : ℝ) ≤ ((14359871831770811581/14365000000000000000 : ℝ)+(276270251039/143650000000000 : ℝ)*((2811/20000 : ℝ)+(5591/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (14359871831770811581/14365000000000000000 : ℝ)+(276270251039/143650000000000 : ℝ)*((2811/20000 : ℝ)+(5591/50000 : ℝ))=(625080232513761/625000000000000 : ℝ) by norm_num, show 1+(36984682907293253/100000000000000000000 : ℝ)+(7362594986704589/50000000000000000000 : ℝ)=(100051709872880702431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36984682907293253/100000000000000000000 : ℝ) ≤ ((14359871831770811581/14365000000000000000 : ℝ)+2*(276270251039/143650000000000 : ℝ)*(2811/20000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (14359871831770811581/14365000000000000000 : ℝ)+2*(276270251039/143650000000000 : ℝ)*(2811/20000 : ℝ)=(5000918130361127/5000000000000000 : ℝ) by norm_num, show 1+2*(36984682907293253/100000000000000000000 : ℝ)=(50036984682907293253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14359871831770811581/14365000000000000000 : ℝ)*(X 1 0+X 2 0)+(276270251039/143650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (14359871831770811581/14365000000000000000 : ℝ)) (alpha := (276270251039/143650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14359871831770811581/14365000000000000000 : ℝ)*(X 0 1+X 2 1)+(276270251039/143650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (14359871831770811581/14365000000000000000 : ℝ)) (alpha := (276270251039/143650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14359871831770811581/14365000000000000000 : ℝ)*(X 0 2+X 1 2)+(276270251039/143650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (14359871831770811581/14365000000000000000 : ℝ)) (alpha := (276270251039/143650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1104324497/5000000000 : ℝ)*X 0 0+(5395127087/10000000000 : ℝ)*X 0 1+(5263706411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334071887/625000000 : ℝ)*X 1 0+(-1137669473/5000000000 : ℝ)*X 1 1+(5263706419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672575003/5000000000 : ℝ)*X 2 0+(5263706537/10000000000 : ℝ)*X 2 1+(-2275339037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875380541/2000000000 : ℝ)*X 0 0+(2125145717/5000000000 : ℝ)*X 0 1+(901469319/2000000000 : ℝ)*X 0 2+(875380541/2000000000 : ℝ)*X 1 0+(2125145717/5000000000 : ℝ)*X 1 1+(901469319/2000000000 : ℝ)*X 1 2+(875380541/2000000000 : ℝ)*X 2 0+(2125145717/5000000000 : ℝ)*X 2 1+(901469319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104327117/5000000000 : ℝ)*X 0 0+(210561537/400000000 : ℝ)*X 0 1+(5394793857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312074307/10000000000 : ℝ)*X 1 0+(-2144251493/10000000000 : ℝ)*X 1 1+(5394793981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83001159/156250000 : ℝ)*X 2 0+(43158353/80000000 : ℝ)*X 2 1+(-85770059/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094228273/2500000000 : ℝ)*X 0 0+(901339409/2000000000 : ℝ)*X 0 1+(4250943183/10000000000 : ℝ)*X 0 2+(1094228273/2500000000 : ℝ)*X 1 0+(901339409/2000000000 : ℝ)*X 1 1+(4250943183/10000000000 : ℝ)*X 1 2+(1094228273/2500000000 : ℝ)*X 2 0+(901339409/2000000000 : ℝ)*X 2 1+(4250943183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206503200508117056207542241/89781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3772453/625000000000 : ℝ)*(base19) + (89851079/25000000000000 : ℝ)*(base23) + (967023/6250000000000 : ℝ)*(upper2) + (68336563/50000000000000 : ℝ)*(upper3) + (718713829167571/12500000000000 : ℝ)*(major0) + (718713829167571/12500000000000 : ℝ)*(major1) + (718713829167571/12500000000000 : ℝ)*(major2) + (3804587163963513/50000000000000 : ℝ)*(sp0) + (1902296392720081/25000000000000 : ℝ)*(sp1) + (3804592232758469/50000000000000 : ℝ)*(sp2) + (972556177954513/25000000000000 : ℝ)*(sp3) + (11846545777/100000000000000 : ℝ)*(sp4) + (1349551549/100000000000000 : ℝ)*(sp6) + (5151860627/50000000000000 : ℝ)*(sp7) + (1945117507769653/50000000000000 : ℝ)*(f.failure) + (1902296543618201/25000000000000 : ℝ)*(f.sum) + (29219638123643/7182500000000000000000000000 : ℝ)*base66 + (187982085416771327/13812500000000000000000000000000 : ℝ)*base67 + (29989123094771327/13812500000000000000000000000000 : ℝ)*base69 + (44284919168583827/13812500000000000000000000000000 : ℝ)*base71 + (19836823263003/7182500000000000000000000000 : ℝ)*base74 + (121229744094708827/13812500000000000000000000000000 : ℝ)*base75 + (222053478685833827/13812500000000000000000000000000 : ℝ)*base77 + (279376098884021327/13812500000000000000000000000000 : ℝ)*base79 + (40133160567161/14365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7377037/2500000000000000000000 : ℝ)*base90 + (7377037/2500000000000000000000 : ℝ)*base92 + (7377037/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24149427347455360774701201/5525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (866387477/100000000000000 : ℝ)*(base19) + (798246111/100000000000000 : ℝ)*(base23) + (154078171/100000000000000 : ℝ)*(upper3) + (10690071/20000000000000 : ℝ)*(lower4) + (70281673/50000000000000 : ℝ)*(upper5) + (577893517746909/10000000000000 : ℝ)*(major0) + (577893517746909/10000000000000 : ℝ)*(major1) + (577893517746909/10000000000000 : ℝ)*(major2) + (25917378817/100000000000000 : ℝ)*(sp1) + (29103865871/100000000000000 : ℝ)*(sp2) + (764786196472789/10000000000000 : ℝ)*(sp4) + (1911958795240399/25000000000000 : ℝ)*(sp5) + (7647832062615909/100000000000000 : ℝ)*(sp6) + (1955004122256189/50000000000000 : ℝ)*(sp7) + (1955004122256189/50000000000000 : ℝ)*(f.failure) + (764786196472789/10000000000000 : ℝ)*(f.sum) + (160034179359/27625000000000000000000000 : ℝ)*base65 + (9893659240119841/850000000000000000000000000000 : ℝ)*base67 + (4336703792719841/850000000000000000000000000000 : ℝ)*base69 + (14801003890919841/850000000000000000000000000000 : ℝ)*base71 + (106814981951/27625000000000000000000000 : ℝ)*base73 + (8636081764069841/850000000000000000000000000000 : ℝ)*base75 + (2806673326980159/850000000000000000000000000000 : ℝ)*base78 + (5006381846580159/850000000000000000000000000000 : ℝ)*base80 + (166378794987/27625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7661781/2500000000000000000000 : ℝ)*base90 + (7661781/2500000000000000000000 : ℝ)*base92 + (7661781/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1056_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s7_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208691759/10000000000 : ℝ)*x 0 + (2697317047/5000000000 : ℝ)*x 1 + (5264171319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208691759/10000000000 : ℝ)^8249 ≤ (13412911695787/100000000000000 : ℝ)^6201 := by
    have hnat : (2208691759 : ℕ)^8249*100000000000000^6201 ≤ 13412911695787^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208691759 10000000000 13412911695787 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697317047/5000000000 : ℝ)^8249 ≤ (21999219302067/50000000000000 : ℝ)^6201 := by
    have hnat : (2697317047 : ℕ)^8249*50000000000000^6201 ≤ 21999219302067^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697317047 5000000000 21999219302067 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264171319/10000000000 : ℝ)^8249 ≤ (21294324839617/50000000000000 : ℝ)^6201 := by
    have hnat : (5264171319 : ℕ)^8249*50000000000000^6201 ≤ 21294324839617^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264171319 10000000000 21294324839617 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208691759/10000000000 : ℝ), (2697317047/5000000000 : ℝ), (5264171319/10000000000 : ℝ)] ![(13412911695787/100000000000000 : ℝ), (21999219302067/50000000000000 : ℝ), (21294324839617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208691759/10000000000 : ℝ)|^8249 ≤ (13412911695787/100000000000000 : ℝ)^6201
        have hw : |(-2208691759/10000000000 : ℝ)|=(2208691759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697317047/5000000000 : ℝ)|^8249 ≤ (21999219302067/50000000000000 : ℝ)^6201
        have hw : |(2697317047/5000000000 : ℝ)|=(2697317047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264171319/10000000000 : ℝ)|^8249 ≤ (21294324839617/50000000000000 : ℝ)^6201
        have hw : |(5264171319/10000000000 : ℝ)|=(5264171319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672513571/5000000000 : ℝ)*x 0 + (-2274889169/10000000000 : ℝ)*x 1 + (5264171031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672513571/5000000000 : ℝ)^8249 ≤ (43461040607453/100000000000000 : ℝ)^6201 := by
    have hnat : (2672513571 : ℕ)^8249*100000000000000^6201 ≤ 43461040607453^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672513571 5000000000 43461040607453 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274889169/10000000000 : ℝ)^8249 ≤ (6975156393179/50000000000000 : ℝ)^6201 := by
    have hnat : (2274889169 : ℕ)^8249*50000000000000^6201 ≤ 6975156393179^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274889169 10000000000 6975156393179 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264171031/10000000000 : ℝ)^8249 ≤ (5323580822463/12500000000000 : ℝ)^6201 := by
    have hnat : (5264171031 : ℕ)^8249*12500000000000^6201 ≤ 5323580822463^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264171031 10000000000 5323580822463 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672513571/5000000000 : ℝ), (-2274889169/10000000000 : ℝ), (5264171031/10000000000 : ℝ)] ![(43461040607453/100000000000000 : ℝ), (6975156393179/50000000000000 : ℝ), (5323580822463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672513571/5000000000 : ℝ)|^8249 ≤ (43461040607453/100000000000000 : ℝ)^6201
        have hw : |(2672513571/5000000000 : ℝ)|=(2672513571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2274889169/10000000000 : ℝ)|^8249 ≤ (6975156393179/50000000000000 : ℝ)^6201
        have hw : |(-2274889169/10000000000 : ℝ)|=(2274889169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264171031/10000000000 : ℝ)|^8249 ≤ (5323580822463/12500000000000 : ℝ)^6201
        have hw : |(5264171031/10000000000 : ℝ)|=(5264171031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534502707/1000000000 : ℝ)*x 0 + (2632085643/5000000000 : ℝ)*x 1 + (-2274888929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534502707/1000000000 : ℝ)^8249 ≤ (2173051991433/5000000000000 : ℝ)^6201 := by
    have hnat : (534502707 : ℕ)^8249*5000000000000^6201 ≤ 2173051991433^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534502707 1000000000 2173051991433 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632085643/5000000000 : ℝ)^8249 ≤ (532358116551/1250000000000 : ℝ)^6201 := by
    have hnat : (2632085643 : ℕ)^8249*1250000000000^6201 ≤ 532358116551^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632085643 5000000000 532358116551 1250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274888929/10000000000 : ℝ)^8249 ≤ (13950310828531/100000000000000 : ℝ)^6201 := by
    have hnat : (2274888929 : ℕ)^8249*100000000000000^6201 ≤ 13950310828531^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274888929 10000000000 13950310828531 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534502707/1000000000 : ℝ), (2632085643/5000000000 : ℝ), (-2274888929/10000000000 : ℝ)] ![(2173051991433/5000000000000 : ℝ), (532358116551/1250000000000 : ℝ), (13950310828531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534502707/1000000000 : ℝ)|^8249 ≤ (2173051991433/5000000000000 : ℝ)^6201
        have hw : |(534502707/1000000000 : ℝ)|=(534502707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632085643/5000000000 : ℝ)|^8249 ≤ (532358116551/1250000000000 : ℝ)^6201
        have hw : |(2632085643/5000000000 : ℝ)|=(2632085643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274888929/10000000000 : ℝ)|^8249 ≤ (13950310828531/100000000000000 : ℝ)^6201
        have hw : |(-2274888929/10000000000 : ℝ)|=(2274888929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188463727/5000000000 : ℝ)*x 0 + (4251224429/10000000000 : ℝ)*x 1 + (901281389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188463727/5000000000 : ℝ)^8249 ≤ (8329110136911/25000000000000 : ℝ)^6201 := by
    have hnat : (2188463727 : ℕ)^8249*25000000000000^6201 ≤ 8329110136911^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188463727 5000000000 8329110136911 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251224429/10000000000 : ℝ)^8249 ≤ (32049674125239/100000000000000 : ℝ)^6201 := by
    have hnat : (4251224429 : ℕ)^8249*100000000000000^6201 ≤ 32049674125239^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251224429 10000000000 32049674125239 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901281389/2000000000 : ℝ)^8249 ≤ (17316942661177/50000000000000 : ℝ)^6201 := by
    have hnat : (901281389 : ℕ)^8249*50000000000000^6201 ≤ 17316942661177^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901281389 2000000000 17316942661177 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188463727/5000000000 : ℝ), (4251224429/10000000000 : ℝ), (901281389/2000000000 : ℝ)] ![(8329110136911/25000000000000 : ℝ), (32049674125239/100000000000000 : ℝ), (17316942661177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188463727/5000000000 : ℝ)|^8249 ≤ (8329110136911/25000000000000 : ℝ)^6201
        have hw : |(2188463727/5000000000 : ℝ)|=(2188463727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251224429/10000000000 : ℝ)|^8249 ≤ (32049674125239/100000000000000 : ℝ)^6201
        have hw : |(4251224429/10000000000 : ℝ)|=(4251224429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901281389/2000000000 : ℝ)|^8249 ≤ (17316942661177/50000000000000 : ℝ)^6201
        have hw : |(901281389/2000000000 : ℝ)|=(901281389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208697003/10000000000 : ℝ)*x 0 + (5264498221/10000000000 : ℝ)*x 1 + (2697152957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208697003/10000000000 : ℝ)^8249 ≤ (2682590811829/20000000000000 : ℝ)^6201 := by
    have hnat : (2208697003 : ℕ)^8249*20000000000000^6201 ≤ 2682590811829^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208697003 10000000000 2682590811829 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264498221/10000000000 : ℝ)^8249 ≤ (10648041979803/25000000000000 : ℝ)^6201 := by
    have hnat : (5264498221 : ℕ)^8249*25000000000000^6201 ≤ 10648041979803^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264498221 10000000000 10648041979803 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697152957/5000000000 : ℝ)^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201 := by
    have hnat : (2697152957 : ℕ)^8249*100000000000000^6201 ≤ 43994878009017^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697152957 5000000000 43994878009017 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208697003/10000000000 : ℝ), (5264498221/10000000000 : ℝ), (2697152957/5000000000 : ℝ)] ![(2682590811829/20000000000000 : ℝ), (10648041979803/25000000000000 : ℝ), (43994878009017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208697003/10000000000 : ℝ)|^8249 ≤ (2682590811829/20000000000000 : ℝ)^6201
        have hw : |(-2208697003/10000000000 : ℝ)|=(2208697003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264498221/10000000000 : ℝ)|^8249 ≤ (10648041979803/25000000000000 : ℝ)^6201
        have hw : |(5264498221/10000000000 : ℝ)|=(5264498221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697152957/5000000000 : ℝ)|^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201
        have hw : |(2697152957/5000000000 : ℝ)|=(2697152957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312192327/10000000000 : ℝ)*x 0 + (-2144754153/10000000000 : ℝ)*x 1 + (2697152957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312192327/10000000000 : ℝ)^8249 ≤ (43106241139787/100000000000000 : ℝ)^6201 := by
    have hnat : (5312192327 : ℕ)^8249*100000000000000^6201 ≤ 43106241139787^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312192327 10000000000 43106241139787 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144754153/10000000000 : ℝ)^8249 ≤ (6449440416867/50000000000000 : ℝ)^6201 := by
    have hnat : (2144754153 : ℕ)^8249*50000000000000^6201 ≤ 6449440416867^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144754153 10000000000 6449440416867 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697152957/5000000000 : ℝ)^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201 := by
    have hnat : (2697152957 : ℕ)^8249*100000000000000^6201 ≤ 43994878009017^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697152957 5000000000 43994878009017 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312192327/10000000000 : ℝ), (-2144754153/10000000000 : ℝ), (2697152957/5000000000 : ℝ)] ![(43106241139787/100000000000000 : ℝ), (6449440416867/50000000000000 : ℝ), (43994878009017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312192327/10000000000 : ℝ)|^8249 ≤ (43106241139787/100000000000000 : ℝ)^6201
        have hw : |(5312192327/10000000000 : ℝ)|=(5312192327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144754153/10000000000 : ℝ)|^8249 ≤ (6449440416867/50000000000000 : ℝ)^6201
        have hw : |(-2144754153/10000000000 : ℝ)|=(2144754153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697152957/5000000000 : ℝ)|^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201
        have hw : |(2697152957/5000000000 : ℝ)|=(2697152957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312192327/10000000000 : ℝ)*x 0 + (2697152957/5000000000 : ℝ)*x 1 + (-2144754153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312192327/10000000000 : ℝ)^8249 ≤ (43106241139787/100000000000000 : ℝ)^6201 := by
    have hnat : (5312192327 : ℕ)^8249*100000000000000^6201 ≤ 43106241139787^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312192327 10000000000 43106241139787 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697152957/5000000000 : ℝ)^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201 := by
    have hnat : (2697152957 : ℕ)^8249*100000000000000^6201 ≤ 43994878009017^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697152957 5000000000 43994878009017 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144754153/10000000000 : ℝ)^8249 ≤ (6449440416867/50000000000000 : ℝ)^6201 := by
    have hnat : (2144754153 : ℕ)^8249*50000000000000^6201 ≤ 6449440416867^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144754153 10000000000 6449440416867 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312192327/10000000000 : ℝ), (2697152957/5000000000 : ℝ), (-2144754153/10000000000 : ℝ)] ![(43106241139787/100000000000000 : ℝ), (43994878009017/100000000000000 : ℝ), (6449440416867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312192327/10000000000 : ℝ)|^8249 ≤ (43106241139787/100000000000000 : ℝ)^6201
        have hw : |(5312192327/10000000000 : ℝ)|=(5312192327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697152957/5000000000 : ℝ)|^8249 ≤ (43994878009017/100000000000000 : ℝ)^6201
        have hw : |(2697152957/5000000000 : ℝ)|=(2697152957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144754153/10000000000 : ℝ)|^8249 ≤ (6449440416867/50000000000000 : ℝ)^6201
        have hw : |(-2144754153/10000000000 : ℝ)|=(2144754153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s7_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218846863/500000000 : ℝ)*x 0 + (1126441743/2500000000 : ℝ)*x 1 + (425186691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218846863/500000000 : ℝ)^8249 ≤ (8329134960289/25000000000000 : ℝ)^6201 := by
    have hnat : (218846863 : ℕ)^8249*25000000000000^6201 ≤ 8329134960289^6201*500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218846863 500000000 8329134960289 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126441743/2500000000 : ℝ)^8249 ≤ (34627342549459/100000000000000 : ℝ)^6201 := by
    have hnat : (1126441743 : ℕ)^8249*100000000000000^6201 ≤ 34627342549459^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126441743 2500000000 34627342549459 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425186691/1000000000 : ℝ)^8249 ≤ (32056117602267/100000000000000 : ℝ)^6201 := by
    have hnat : (425186691 : ℕ)^8249*100000000000000^6201 ≤ 32056117602267^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425186691 1000000000 32056117602267 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218846863/500000000 : ℝ), (1126441743/2500000000 : ℝ), (425186691/1000000000 : ℝ)] ![(8329134960289/25000000000000 : ℝ), (34627342549459/100000000000000 : ℝ), (32056117602267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218846863/500000000 : ℝ)|^8249 ≤ (8329134960289/25000000000000 : ℝ)^6201
        have hw : |(218846863/500000000 : ℝ)|=(218846863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126441743/2500000000 : ℝ)|^8249 ≤ (34627342549459/100000000000000 : ℝ)^6201
        have hw : |(1126441743/2500000000 : ℝ)|=(1126441743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425186691/1000000000 : ℝ)|^8249 ≤ (32056117602267/100000000000000 : ℝ)^6201
        have hw : |(425186691/1000000000 : ℝ)|=(425186691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (7479968117705237/50000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^1031 ≤ (7479968117705237/50000000000000000000 : ℝ)^256 := by
      have hnat : (5613 : ℕ)^1031*50000000000000000000^256 ≤ 7479968117705237^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 7479968117705237 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (7479968117705237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (1031/256 : ℝ) ≤ (9124900130580491/25000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^1031 ≤ (9124900130580491/25000000000000000000 : ℝ)^256 := by
      have hnat : (14009 : ℕ)^1031*25000000000000000000^256 ≤ 9124900130580491^256*100000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 9124900130580491 25000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (9124900130580491/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007479968117705237/25000000000000000000 : ℝ) ≤ (2500185708684947/2500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25007479968117705237/25000000000000000000 : ℝ)^256 ≤ (2500185708684947/2500000000000000 : ℝ)^1031 := by
      have hnat : (25007479968117705237 : ℕ)^256*2500000000000000^1031 ≤ 2500185708684947^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007479968117705237 25000000000000000000 2500185708684947 2500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185708684947/2500000000000000 : ℝ)) (X := (25007479968117705237/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025729768378866219/50000000000000000000 : ℝ) ≤ (10001277506717883/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50025729768378866219/50000000000000000000 : ℝ)^256 ≤ (10001277506717883/10000000000000000 : ℝ)^1031 := by
      have hnat : (50025729768378866219 : ℕ)^256*10000000000000000^1031 ≤ 10001277506717883^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025729768378866219 50000000000000000000 10001277506717883 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277506717883/10000000000000000 : ℝ)) (X := (50025729768378866219/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509124900130580491/12500000000000000000 : ℝ) ≤ (5000906089347989/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (12509124900130580491/12500000000000000000 : ℝ)^256 ≤ (5000906089347989/5000000000000000 : ℝ)^1031 := by
      have hnat : (12509124900130580491 : ℕ)^256*5000000000000000^1031 ≤ 5000906089347989^1031*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509124900130580491 12500000000000000000 5000906089347989 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000906089347989/5000000000000000 : ℝ)) (X := (12509124900130580491/12500000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7479968117705237/50000000000000000000 : ℝ) ≤ ((3477507856728580133/3478750000000000000 : ℝ)+2*(106934395619/55660000000000 : ℝ)*(5613/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3477507856728580133/3478750000000000000 : ℝ)+2*(106934395619/55660000000000 : ℝ)*(5613/50000 : ℝ)=(2500185708684947/2500000000000000 : ℝ) by norm_num, show 1+2*(7479968117705237/50000000000000000000 : ℝ)=(25007479968117705237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9124900130580491/25000000000000000000 : ℝ)+(7479968117705237/50000000000000000000 : ℝ) ≤ ((3477507856728580133/3478750000000000000 : ℝ)+(106934395619/55660000000000 : ℝ)*((14009/100000 : ℝ)+(5613/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (3477507856728580133/3478750000000000000 : ℝ)+(106934395619/55660000000000 : ℝ)*((14009/100000 : ℝ)+(5613/50000 : ℝ))=(10001277506717883/10000000000000000 : ℝ) by norm_num, show 1+(9124900130580491/25000000000000000000 : ℝ)+(7479968117705237/50000000000000000000 : ℝ)=(50025729768378866219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9124900130580491/25000000000000000000 : ℝ) ≤ ((3477507856728580133/3478750000000000000 : ℝ)+2*(106934395619/55660000000000 : ℝ)*(14009/100000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3477507856728580133/3478750000000000000 : ℝ)+2*(106934395619/55660000000000 : ℝ)*(14009/100000 : ℝ)=(5000906089347989/5000000000000000 : ℝ) by norm_num, show 1+2*(9124900130580491/25000000000000000000 : ℝ)=(12509124900130580491/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3477507856728580133/3478750000000000000 : ℝ)*(X 1 0+X 2 0)+(106934395619/55660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (3477507856728580133/3478750000000000000 : ℝ)) (alpha := (106934395619/55660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3477507856728580133/3478750000000000000 : ℝ)*(X 0 1+X 2 1)+(106934395619/55660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (3477507856728580133/3478750000000000000 : ℝ)) (alpha := (106934395619/55660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3477507856728580133/3478750000000000000 : ℝ)*(X 0 2+X 1 2)+(106934395619/55660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (3477507856728580133/3478750000000000000 : ℝ)) (alpha := (106934395619/55660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2208691759/10000000000 : ℝ)*X 0 0+(2697317047/5000000000 : ℝ)*X 0 1+(5264171319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672513571/5000000000 : ℝ)*X 1 0+(-2274889169/10000000000 : ℝ)*X 1 1+(5264171031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534502707/1000000000 : ℝ)*X 2 0+(2632085643/5000000000 : ℝ)*X 2 1+(-2274888929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188463727/5000000000 : ℝ)*X 0 0+(4251224429/10000000000 : ℝ)*X 0 1+(901281389/2000000000 : ℝ)*X 0 2+(2188463727/5000000000 : ℝ)*X 1 0+(4251224429/10000000000 : ℝ)*X 1 1+(901281389/2000000000 : ℝ)*X 1 2+(2188463727/5000000000 : ℝ)*X 2 0+(4251224429/10000000000 : ℝ)*X 2 1+(901281389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2208697003/10000000000 : ℝ)*X 0 0+(5264498221/10000000000 : ℝ)*X 0 1+(2697152957/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312192327/10000000000 : ℝ)*X 1 0+(-2144754153/10000000000 : ℝ)*X 1 1+(2697152957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312192327/10000000000 : ℝ)*X 2 0+(2697152957/5000000000 : ℝ)*X 2 1+(-2144754153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218846863/500000000 : ℝ)*X 0 0+(1126441743/2500000000 : ℝ)*X 0 1+(425186691/1000000000 : ℝ)*X 0 2+(218846863/500000000 : ℝ)*X 1 0+(1126441743/2500000000 : ℝ)*X 1 1+(425186691/1000000000 : ℝ)*X 1 2+(218846863/500000000 : ℝ)*X 2 0+(1126441743/2500000000 : ℝ)*X 2 1+(425186691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8205090785000950408671/695750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1033086341/50000000000000 : ℝ)*(base19) + (734273459/50000000000000 : ℝ)*(base23) + (132121957/50000000000000 : ℝ)*(lower2) + (117078419/50000000000000 : ℝ)*(upper3) + (27831609/12500000000000 : ℝ)*(upper5) + (579195797144417/10000000000000 : ℝ)*(major0) + (579195797144417/10000000000000 : ℝ)*(major1) + (579195797144417/10000000000000 : ℝ)*(major2) + (7665055891666907/100000000000000 : ℝ)*(sp0) + (3832547030089547/50000000000000 : ℝ)*(sp1) + (3832547328902429/50000000000000 : ℝ)*(sp2) + (979697590164831/25000000000000 : ℝ)*(sp3) + (10058671217/25000000000000 : ℝ)*(sp4) + (2906277191/10000000000000 : ℝ)*(sp7) + (1959409711715617/50000000000000 : ℝ)*(f.failure) + (239534253948493/3125000000000 : ℝ)*(f.sum) + (19877818910573/2783000000000000000000000000 : ℝ)*base65 + (154776200648679961/34787500000000000000000000000000 : ℝ)*base67 + (166087118341682539/34787500000000000000000000000000 : ℝ)*base70 + (581594726239895039/34787500000000000000000000000000 : ℝ)*base72 + (883980263547/139150000000000000000000000 : ℝ)*base73 + (1121152092341979961/34787500000000000000000000000000 : ℝ)*base75 + (323696502891404961/34787500000000000000000000000000 : ℝ)*base77 + (269616003357145039/34787500000000000000000000000000 : ℝ)*base80 + (1559995500549/695750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5615207/2500000000000000000000 : ℝ)*base89 + (5615207/2500000000000000000000 : ℝ)*base91 + (5615207/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130219050175064420438314923/17393750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348412161/25000000000000 : ℝ)*(base19) + (15161937/1000000000000 : ℝ)*(base23) + (7489187/5000000000000 : ℝ)*(upper3) + (11150179/20000000000000 : ℝ)*(lower4) + (76270513/50000000000000 : ℝ)*(upper5) + (1164225962384123/20000000000000 : ℝ)*(major0) + (1164225962384123/20000000000000 : ℝ)*(major1) + (1164225962384123/20000000000000 : ℝ)*(major2) + (7562740729/20000000000000 : ℝ)*(sp1) + (40660587147/100000000000000 : ℝ)*(sp2) + (962962797625063/12500000000000 : ℝ)*(sp4) + (1540732634729643/20000000000000 : ℝ)*(sp5) + (962957525527457/12500000000000 : ℝ)*(sp6) + (1969278496644647/50000000000000 : ℝ)*(sp7) + (1969278496644647/50000000000000 : ℝ)*(f.failure) + (962962797625063/12500000000000 : ℝ)*(f.sum) + (21000901871061/2783000000000000000000000000 : ℝ)*base65 + (995966595003090859/69575000000000000000000000000000 : ℝ)*base67 + (307512156866790859/69575000000000000000000000000000 : ℝ)*base69 + (538944270370865859/69575000000000000000000000000000 : ℝ)*base71 + (15611942583041/2783000000000000000000000000 : ℝ)*base73 + (944418364952384141/69575000000000000000000000000000 : ℝ)*base76 + (257494616591340859/69575000000000000000000000000000 : ℝ)*base77 + (1570252334440940859/69575000000000000000000000000000 : ℝ)*base79 + (3550980334419/1391500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15647663/2500000000000000000000 : ℝ)*base90 + (15647663/2500000000000000000000 : ℝ)*base92 + (15647663/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1056_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_s8_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-552175693/2500000000 : ℝ)*x 0 + (1078906171/2000000000 : ℝ)*x 1 + (5264267129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552175693/2500000000 : ℝ)^8249 ≤ (3353250165931/25000000000000 : ℝ)^6201 := by
    have hnat : (552175693 : ℕ)^8249*25000000000000^6201 ≤ 3353250165931^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552175693 2500000000 3353250165931 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078906171/2000000000 : ℝ)^8249 ≤ (21998659251469/50000000000000 : ℝ)^6201 := by
    have hnat : (1078906171 : ℕ)^8249*50000000000000^6201 ≤ 21998659251469^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078906171 2000000000 21998659251469 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264267129/10000000000 : ℝ)^8249 ≤ (42589680814341/100000000000000 : ℝ)^6201 := by
    have hnat : (5264267129 : ℕ)^8249*100000000000000^6201 ≤ 42589680814341^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264267129 10000000000 42589680814341 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552175693/2500000000 : ℝ), (1078906171/2000000000 : ℝ), (5264267129/10000000000 : ℝ)] ![(3353250165931/25000000000000 : ℝ), (21998659251469/50000000000000 : ℝ), (42589680814341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552175693/2500000000 : ℝ)|^8249 ≤ (3353250165931/25000000000000 : ℝ)^6201
        have hw : |(-552175693/2500000000 : ℝ)|=(552175693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078906171/2000000000 : ℝ)|^8249 ≤ (21998659251469/50000000000000 : ℝ)^6201
        have hw : |(1078906171/2000000000 : ℝ)|=(1078906171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264267129/10000000000 : ℝ)|^8249 ≤ (42589680814341/100000000000000 : ℝ)^6201
        have hw : |(5264267129/10000000000 : ℝ)|=(5264267129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668125107/1250000000 : ℝ)*x 0 + (-142174827/625000000 : ℝ)*x 1 + (5264267137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668125107/1250000000 : ℝ)^8249 ≤ (21730378141593/50000000000000 : ℝ)^6201 := by
    have hnat : (668125107 : ℕ)^8249*50000000000000^6201 ≤ 21730378141593^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668125107 1250000000 21730378141593 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142174827/625000000 : ℝ)^8249 ≤ (13949562804593/100000000000000 : ℝ)^6201 := by
    have hnat : (142174827 : ℕ)^8249*100000000000000^6201 ≤ 13949562804593^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142174827 625000000 13949562804593 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264267137/10000000000 : ℝ)^8249 ≤ (1064742022511/2500000000000 : ℝ)^6201 := by
    have hnat : (5264267137 : ℕ)^8249*2500000000000^6201 ≤ 1064742022511^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264267137 10000000000 1064742022511 2500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668125107/1250000000 : ℝ), (-142174827/625000000 : ℝ), (5264267137/10000000000 : ℝ)] ![(21730378141593/50000000000000 : ℝ), (13949562804593/100000000000000 : ℝ), (1064742022511/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668125107/1250000000 : ℝ)|^8249 ≤ (21730378141593/50000000000000 : ℝ)^6201
        have hw : |(668125107/1250000000 : ℝ)|=(668125107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142174827/625000000 : ℝ)|^8249 ≤ (13949562804593/100000000000000 : ℝ)^6201
        have hw : |(-142174827/625000000 : ℝ)|=(142174827/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264267137/10000000000 : ℝ)|^8249 ≤ (1064742022511/2500000000000 : ℝ)^6201
        have hw : |(5264267137/10000000000 : ℝ)|=(5264267137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345000889/10000000000 : ℝ)*x 0 + (5264267073/10000000000 : ℝ)*x 1 + (-284349659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345000889/10000000000 : ℝ)^8249 ≤ (10865189160033/25000000000000 : ℝ)^6201 := by
    have hnat : (5345000889 : ℕ)^8249*25000000000000^6201 ≤ 10865189160033^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345000889 10000000000 10865189160033 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264267073/10000000000 : ℝ)^8249 ≤ (42589680211651/100000000000000 : ℝ)^6201 := by
    have hnat : (5264267073 : ℕ)^8249*100000000000000^6201 ≤ 42589680211651^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264267073 10000000000 42589680211651 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284349659/1250000000 : ℝ)^8249 ≤ (13949563130893/100000000000000 : ℝ)^6201 := by
    have hnat : (284349659 : ℕ)^8249*100000000000000^6201 ≤ 13949563130893^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284349659 1250000000 13949563130893 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345000889/10000000000 : ℝ), (5264267073/10000000000 : ℝ), (-284349659/1250000000 : ℝ)] ![(10865189160033/25000000000000 : ℝ), (42589680211651/100000000000000 : ℝ), (13949563130893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345000889/10000000000 : ℝ)|^8249 ≤ (10865189160033/25000000000000 : ℝ)^6201
        have hw : |(5345000889/10000000000 : ℝ)|=(5345000889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264267073/10000000000 : ℝ)|^8249 ≤ (42589680211651/100000000000000 : ℝ)^6201
        have hw : |(5264267073/10000000000 : ℝ)|=(5264267073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284349659/1250000000 : ℝ)|^8249 ≤ (13949563130893/100000000000000 : ℝ)^6201
        have hw : |(-284349659/1250000000 : ℝ)|=(284349659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376932383/10000000000 : ℝ)*x 0 + (4251419103/10000000000 : ℝ)*x 1 + (4506211097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376932383/10000000000 : ℝ)^8249 ≤ (33316490457661/100000000000000 : ℝ)^6201 := by
    have hnat : (4376932383 : ℕ)^8249*100000000000000^6201 ≤ 33316490457661^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376932383 10000000000 33316490457661 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251419103/10000000000 : ℝ)^8249 ≤ (6410325297491/20000000000000 : ℝ)^6201 := by
    have hnat : (4251419103 : ℕ)^8249*20000000000000^6201 ≤ 6410325297491^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251419103 10000000000 6410325297491 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506211097/10000000000 : ℝ)^8249 ≤ (6926376607001/20000000000000 : ℝ)^6201 := by
    have hnat : (4506211097 : ℕ)^8249*20000000000000^6201 ≤ 6926376607001^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506211097 10000000000 6926376607001 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376932383/10000000000 : ℝ), (4251419103/10000000000 : ℝ), (4506211097/10000000000 : ℝ)] ![(33316490457661/100000000000000 : ℝ), (6410325297491/20000000000000 : ℝ), (6926376607001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376932383/10000000000 : ℝ)|^8249 ≤ (33316490457661/100000000000000 : ℝ)^6201
        have hw : |(4376932383/10000000000 : ℝ)|=(4376932383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251419103/10000000000 : ℝ)|^8249 ≤ (6410325297491/20000000000000 : ℝ)^6201
        have hw : |(4251419103/10000000000 : ℝ)|=(4251419103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506211097/10000000000 : ℝ)|^8249 ≤ (6926376607001/20000000000000 : ℝ)^6201
        have hw : |(4506211097/10000000000 : ℝ)|=(4506211097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104353947/5000000000 : ℝ)*x 0 + (5264593279/10000000000 : ℝ)*x 1 + (1348550877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104353947/5000000000 : ℝ)^8249 ≤ (670652102079/5000000000000 : ℝ)^6201 := by
    have hnat : (1104353947 : ℕ)^8249*5000000000000^6201 ≤ 670652102079^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104353947 5000000000 670652102079 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264593279/10000000000 : ℝ)^8249 ≤ (21296595491017/50000000000000 : ℝ)^6201 := by
    have hnat : (5264593279 : ℕ)^8249*50000000000000^6201 ≤ 21296595491017^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264593279 10000000000 21296595491017 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348550877/2500000000 : ℝ)^8249 ≤ (43993766967829/100000000000000 : ℝ)^6201 := by
    have hnat : (1348550877 : ℕ)^8249*100000000000000^6201 ≤ 43993766967829^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348550877 2500000000 43993766967829 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104353947/5000000000 : ℝ), (5264593279/10000000000 : ℝ), (1348550877/2500000000 : ℝ)] ![(670652102079/5000000000000 : ℝ), (21296595491017/50000000000000 : ℝ), (43993766967829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104353947/5000000000 : ℝ)|^8249 ≤ (670652102079/5000000000000 : ℝ)^6201
        have hw : |(-1104353947/5000000000 : ℝ)|=(1104353947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264593279/10000000000 : ℝ)|^8249 ≤ (21296595491017/50000000000000 : ℝ)^6201
        have hw : |(5264593279/10000000000 : ℝ)|=(5264593279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348550877/2500000000 : ℝ)|^8249 ≤ (43993766967829/100000000000000 : ℝ)^6201
        have hw : |(1348550877/2500000000 : ℝ)|=(1348550877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656108091/5000000000 : ℝ)*x 0 + (-2144860843/10000000000 : ℝ)*x 1 + (1078840701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656108091/5000000000 : ℝ)^8249 ≤ (8621299728959/20000000000000 : ℝ)^6201 := by
    have hnat : (2656108091 : ℕ)^8249*20000000000000^6201 ≤ 8621299728959^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656108091 5000000000 8621299728959 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144860843/10000000000 : ℝ)^8249 ≤ (3224933602027/25000000000000 : ℝ)^6201 := by
    have hnat : (2144860843 : ℕ)^8249*25000000000000^6201 ≤ 3224933602027^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144860843 10000000000 3224933602027 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078840701/2000000000 : ℝ)^8249 ≤ (43993766935281/100000000000000 : ℝ)^6201 := by
    have hnat : (1078840701 : ℕ)^8249*100000000000000^6201 ≤ 43993766935281^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078840701 2000000000 43993766935281 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656108091/5000000000 : ℝ), (-2144860843/10000000000 : ℝ), (1078840701/2000000000 : ℝ)] ![(8621299728959/20000000000000 : ℝ), (3224933602027/25000000000000 : ℝ), (43993766935281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656108091/5000000000 : ℝ)|^8249 ≤ (8621299728959/20000000000000 : ℝ)^6201
        have hw : |(2656108091/5000000000 : ℝ)|=(2656108091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144860843/10000000000 : ℝ)|^8249 ≤ (3224933602027/25000000000000 : ℝ)^6201
        have hw : |(-2144860843/10000000000 : ℝ)|=(2144860843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078840701/2000000000 : ℝ)|^8249 ≤ (43993766935281/100000000000000 : ℝ)^6201
        have hw : |(1078840701/2000000000 : ℝ)|=(1078840701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328054043/2500000000 : ℝ)*x 0 + (5394203509/10000000000 : ℝ)*x 1 + (-2144860851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328054043/2500000000 : ℝ)^8249 ≤ (43106498536849/100000000000000 : ℝ)^6201 := by
    have hnat : (1328054043 : ℕ)^8249*100000000000000^6201 ≤ 43106498536849^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328054043 2500000000 43106498536849 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394203509/10000000000 : ℝ)^8249 ≤ (21996883489339/50000000000000 : ℝ)^6201 := by
    have hnat : (5394203509 : ℕ)^8249*50000000000000^6201 ≤ 21996883489339^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394203509 10000000000 21996883489339 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144860851/10000000000 : ℝ)^8249 ≤ (806233404507/6250000000000 : ℝ)^6201 := by
    have hnat : (2144860851 : ℕ)^8249*6250000000000^6201 ≤ 806233404507^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144860851 10000000000 806233404507 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328054043/2500000000 : ℝ), (5394203509/10000000000 : ℝ), (-2144860851/10000000000 : ℝ)] ![(43106498536849/100000000000000 : ℝ), (21996883489339/50000000000000 : ℝ), (806233404507/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328054043/2500000000 : ℝ)|^8249 ≤ (43106498536849/100000000000000 : ℝ)^6201
        have hw : |(1328054043/2500000000 : ℝ)|=(1328054043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394203509/10000000000 : ℝ)|^8249 ≤ (21996883489339/50000000000000 : ℝ)^6201
        have hw : |(5394203509/10000000000 : ℝ)|=(5394203509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144860851/10000000000 : ℝ)|^8249 ≤ (806233404507/6250000000000 : ℝ)^6201
        have hw : |(-2144860851/10000000000 : ℝ)|=(2144860851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s8_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437694229/1000000000 : ℝ)*x 0 + (1126393299/2500000000 : ℝ)*x 1 + (531507419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437694229/1000000000 : ℝ)^8249 ≤ (6663318154783/20000000000000 : ℝ)^6201 := by
    have hnat : (437694229 : ℕ)^8249*20000000000000^6201 ≤ 6663318154783^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437694229 1000000000 6663318154783 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126393299/2500000000 : ℝ)^8249 ≤ (34625361538351/100000000000000 : ℝ)^6201 := by
    have hnat : (1126393299 : ℕ)^8249*100000000000000^6201 ≤ 34625361538351^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126393299 2500000000 34625361538351 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531507419/1250000000 : ℝ)^8249 ≤ (32058047676179/100000000000000 : ℝ)^6201 := by
    have hnat : (531507419 : ℕ)^8249*100000000000000^6201 ≤ 32058047676179^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531507419 1250000000 32058047676179 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437694229/1000000000 : ℝ), (1126393299/2500000000 : ℝ), (531507419/1250000000 : ℝ)] ![(6663318154783/20000000000000 : ℝ), (34625361538351/100000000000000 : ℝ), (32058047676179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437694229/1000000000 : ℝ)|^8249 ≤ (6663318154783/20000000000000 : ℝ)^6201
        have hw : |(437694229/1000000000 : ℝ)|=(437694229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126393299/2500000000 : ℝ)|^8249 ≤ (34625361538351/100000000000000 : ℝ)^6201
        have hw : |(1126393299/2500000000 : ℝ)|=(1126393299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531507419/1250000000 : ℝ)|^8249 ≤ (32058047676179/100000000000000 : ℝ)^6201
        have hw : |(531507419/1250000000 : ℝ)|=(531507419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/20000 : ℝ) ^ (1031/256 : ℝ) ≤ (3752074243011767/25000000000000000000 : ℝ) := by
    have hpowers : (2247/20000 : ℝ)^1031 ≤ (3752074243011767/25000000000000000000 : ℝ)^256 := by
      have hnat : (2247 : ℕ)^1031*25000000000000000000^256 ≤ 3752074243011767^256*20000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 20000 3752074243011767 25000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/20000 : ℝ)) (X := (3752074243011767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (1031/256 : ℝ) ≤ (36394783843719647/100000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^1031 ≤ (36394783843719647/100000000000000000000 : ℝ)^256 := by
      have hnat : (13999 : ℕ)^1031*100000000000000000000^256 ≤ 36394783843719647^256*100000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 36394783843719647 100000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (36394783843719647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503752074243011767/12500000000000000000 : ℝ) ≤ (10000745235818427/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (12503752074243011767/12500000000000000000 : ℝ)^256 ≤ (10000745235818427/10000000000000000 : ℝ)^1031 := by
      have hnat : (12503752074243011767 : ℕ)^256*10000000000000000^1031 ≤ 10000745235818427^1031*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503752074243011767 12500000000000000000 10000745235818427 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000745235818427/10000000000000000 : ℝ)) (X := (12503752074243011767/12500000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010280616163153343/20000000000000000000 : ℝ) ≤ (1250159513180471/1250000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (20010280616163153343/20000000000000000000 : ℝ)^256 ≤ (1250159513180471/1250000000000000 : ℝ)^1031 := by
      have hnat : (20010280616163153343 : ℕ)^256*1250000000000000^1031 ≤ 1250159513180471^1031*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010280616163153343 20000000000000000000 1250159513180471 1250000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159513180471/1250000000000000 : ℝ)) (X := (20010280616163153343/20000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036394783843719647/50000000000000000000 : ℝ) ≤ (10001806975069109/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50036394783843719647/50000000000000000000 : ℝ)^256 ≤ (10001806975069109/10000000000000000 : ℝ)^1031 := by
      have hnat : (50036394783843719647 : ℕ)^256*10000000000000000^1031 ≤ 10001806975069109^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036394783843719647 50000000000000000000 10001806975069109 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001806975069109/10000000000000000 : ℝ)) (X := (50036394783843719647/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3752074243011767/25000000000000000000 : ℝ) ≤ ((13815065595660359979/13820000000000000000 : ℝ)+2*(530869625341/276400000000000 : ℝ)*(2247/20000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (13815065595660359979/13820000000000000000 : ℝ)+2*(530869625341/276400000000000 : ℝ)*(2247/20000 : ℝ)=(10000745235818427/10000000000000000 : ℝ) by norm_num, show 1+2*(3752074243011767/25000000000000000000 : ℝ)=(12503752074243011767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36394783843719647/100000000000000000000 : ℝ)+(3752074243011767/25000000000000000000 : ℝ) ≤ ((13815065595660359979/13820000000000000000 : ℝ)+(530869625341/276400000000000 : ℝ)*((13999/100000 : ℝ)+(2247/20000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (13815065595660359979/13820000000000000000 : ℝ)+(530869625341/276400000000000 : ℝ)*((13999/100000 : ℝ)+(2247/20000 : ℝ))=(1250159513180471/1250000000000000 : ℝ) by norm_num, show 1+(36394783843719647/100000000000000000000 : ℝ)+(3752074243011767/25000000000000000000 : ℝ)=(20010280616163153343/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36394783843719647/100000000000000000000 : ℝ) ≤ ((13815065595660359979/13820000000000000000 : ℝ)+2*(530869625341/276400000000000 : ℝ)*(13999/100000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (13815065595660359979/13820000000000000000 : ℝ)+2*(530869625341/276400000000000 : ℝ)*(13999/100000 : ℝ)=(10001806975069109/10000000000000000 : ℝ) by norm_num, show 1+2*(36394783843719647/100000000000000000000 : ℝ)=(50036394783843719647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13815065595660359979/13820000000000000000 : ℝ)*(X 1 0+X 2 0)+(530869625341/276400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13815065595660359979/13820000000000000000 : ℝ)) (alpha := (530869625341/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13815065595660359979/13820000000000000000 : ℝ)*(X 0 1+X 2 1)+(530869625341/276400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13815065595660359979/13820000000000000000 : ℝ)) (alpha := (530869625341/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13815065595660359979/13820000000000000000 : ℝ)*(X 0 2+X 1 2)+(530869625341/276400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (13815065595660359979/13820000000000000000 : ℝ)) (alpha := (530869625341/276400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552175693/2500000000 : ℝ)*X 0 0+(1078906171/2000000000 : ℝ)*X 0 1+(5264267129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668125107/1250000000 : ℝ)*X 1 0+(-142174827/625000000 : ℝ)*X 1 1+(5264267137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345000889/10000000000 : ℝ)*X 2 0+(5264267073/10000000000 : ℝ)*X 2 1+(-284349659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376932383/10000000000 : ℝ)*X 0 0+(4251419103/10000000000 : ℝ)*X 0 1+(4506211097/10000000000 : ℝ)*X 0 2+(4376932383/10000000000 : ℝ)*X 1 0+(4251419103/10000000000 : ℝ)*X 1 1+(4506211097/10000000000 : ℝ)*X 1 2+(4376932383/10000000000 : ℝ)*X 2 0+(4251419103/10000000000 : ℝ)*X 2 1+(4506211097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104353947/5000000000 : ℝ)*X 0 0+(5264593279/10000000000 : ℝ)*X 0 1+(1348550877/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656108091/5000000000 : ℝ)*X 1 0+(-2144860843/10000000000 : ℝ)*X 1 1+(1078840701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328054043/2500000000 : ℝ)*X 2 0+(5394203509/10000000000 : ℝ)*X 2 1+(-2144860851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437694229/1000000000 : ℝ)*X 0 0+(1126393299/2500000000 : ℝ)*X 0 1+(531507419/1250000000 : ℝ)*X 0 2+(437694229/1000000000 : ℝ)*X 1 0+(1126393299/2500000000 : ℝ)*X 1 1+(531507419/1250000000 : ℝ)*X 1 2+(437694229/1000000000 : ℝ)*X 2 0+(1126393299/2500000000 : ℝ)*X 2 1+(531507419/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69856168948090695840229731/34550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43268069/12500000000000 : ℝ)*(base19) + (1877121/500000000000 : ℝ)*(base23) + (32422763/100000000000000 : ℝ)*(lower2) + (67701209/100000000000000 : ℝ)*(upper3) + (44413/195312500000 : ℝ)*(lower4) + (290038276466721/5000000000000 : ℝ)*(major0) + (290038276466721/5000000000000 : ℝ)*(major1) + (290038276466721/5000000000000 : ℝ)*(major2) + (1919186131373911/25000000000000 : ℝ)*(sp0) + (3838376028718899/50000000000000 : ℝ)*(sp1) + (153535040563163/2000000000000 : ℝ)*(sp2) + (98119336869931/2500000000000 : ℝ)*(sp3) + (3939043353/50000000000000 : ℝ)*(sp4) + (1278223259/25000000000000 : ℝ)*(sp7) + (3924778587690277/100000000000000 : ℝ)*(f.failure) + (153535048071647/2000000000000 : ℝ)*(f.sum) + (1089597545487/691000000000000000000000000 : ℝ)*base66 + (37239026950191141/69100000000000000000000000000000 : ℝ)*base68 + (350608377294791141/69100000000000000000000000000000 : ℝ)*base70 + (426823934039991141/69100000000000000000000000000000 : ℝ)*base72 + (702006101621/691000000000000000000000000 : ℝ)*base73 + (313141915192991141/69100000000000000000000000000000 : ℝ)*base76 + (655257496144191141/69100000000000000000000000000000 : ℝ)*base78 + (615512766549791141/69100000000000000000000000000000 : ℝ)*base80 + (62319026171/691000000000000000000000000 : ℝ)*base82 + (44088067/5000000000000000000000 : ℝ)*base89 + (44088067/5000000000000000000000 : ℝ)*base91 + (44088067/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1566143321377526131119074277/172750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1690947597/100000000000000 : ℝ)*(base19) + (1813191437/100000000000000 : ℝ)*(base23) + (35710549/20000000000000 : ℝ)*(upper3) + (63250173/100000000000000 : ℝ)*(lower4) + (175983633/100000000000000 : ℝ)*(upper5) + (2914998999866179/50000000000000 : ℝ)*(major0) + (2914998999866179/50000000000000 : ℝ)*(major1) + (2914998999866179/50000000000000 : ℝ)*(major2) + (46018576993/100000000000000 : ℝ)*(sp1) + (48886875627/100000000000000 : ℝ)*(sp2) + (1928859629428879/25000000000000 : ℝ)*(sp4) + (3857695404095463/50000000000000 : ℝ)*(sp5) + (7715387817648453/100000000000000 : ℝ)*(sp6) + (246534823721923/6250000000000 : ℝ)*(sp7) + (246534823721923/6250000000000 : ℝ)*(f.failure) + (1928859629428879/25000000000000 : ℝ)*(f.sum) + (15468688082521/6910000000000000000000000000 : ℝ)*base66 + (4516976657097200241/691000000000000000000000000000000 : ℝ)*base67 + (1441279705445200241/691000000000000000000000000000000 : ℝ)*base69 + (8299014679409200241/691000000000000000000000000000000 : ℝ)*base71 + (26711851352099/6910000000000000000000000000 : ℝ)*base73 + (4938192626232200241/691000000000000000000000000000000 : ℝ)*base75 + (7569910328120200241/691000000000000000000000000000000 : ℝ)*base77 + (5430475802246799759/691000000000000000000000000000000 : ℝ)*base80 + (8449398644951/6910000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2331867/312500000000000000000 : ℝ)*base90 + (2331867/312500000000000000000 : ℝ)*base92 + (2331867/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1056_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1056_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1056_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1056_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1056_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
