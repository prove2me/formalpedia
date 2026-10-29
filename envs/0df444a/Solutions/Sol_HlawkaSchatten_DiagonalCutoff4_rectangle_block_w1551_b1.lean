-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:07.046183+00:00
-- url     : https://prove2.me/submissions/202afebd-5986-4e4a-b2e4-bd13c090f4f3

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
theorem support_rectangle_w1551_s3_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811589533/10000000000 : ℝ)*x 0 + (2715147203/5000000000 : ℝ)*x 1 + (2608746679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811589533/10000000000 : ℝ)^4599 ≤ (5552815329109/50000000000000 : ℝ)^3575 := by
    have hnat : (1811589533 : ℕ)^4599*50000000000000^3575 ≤ 5552815329109^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811589533 10000000000 5552815329109 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715147203/5000000000 : ℝ)^4599 ≤ (22794910628637/50000000000000 : ℝ)^3575 := by
    have hnat : (2715147203 : ℕ)^4599*50000000000000^3575 ≤ 22794910628637^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715147203 5000000000 22794910628637 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608746679/5000000000 : ℝ)^4599 ≤ (5413068508791/12500000000000 : ℝ)^3575 := by
    have hnat : (2608746679 : ℕ)^4599*12500000000000^3575 ≤ 5413068508791^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608746679 5000000000 5413068508791 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811589533/10000000000 : ℝ), (2715147203/5000000000 : ℝ), (2608746679/5000000000 : ℝ)] ![(5552815329109/50000000000000 : ℝ), (22794910628637/50000000000000 : ℝ), (5413068508791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811589533/10000000000 : ℝ)|^4599 ≤ (5552815329109/50000000000000 : ℝ)^3575
        have hw : |(-1811589533/10000000000 : ℝ)|=(1811589533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715147203/5000000000 : ℝ)|^4599 ≤ (22794910628637/50000000000000 : ℝ)^3575
        have hw : |(2715147203/5000000000 : ℝ)|=(2715147203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608746679/5000000000 : ℝ)|^4599 ≤ (5413068508791/12500000000000 : ℝ)^3575
        have hw : |(2608746679/5000000000 : ℝ)|=(2608746679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534989197/1000000000 : ℝ)*x 0 + (-960270409/5000000000 : ℝ)*x 1 + (326093333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534989197/1000000000 : ℝ)^4599 ≤ (11180826651187/25000000000000 : ℝ)^3575 := by
    have hnat : (534989197 : ℕ)^4599*25000000000000^3575 ≤ 11180826651187^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534989197 1000000000 11180826651187 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960270409/5000000000 : ℝ)^4599 ≤ (748259102399/6250000000000 : ℝ)^3575 := by
    have hnat : (960270409 : ℕ)^4599*6250000000000^3575 ≤ 748259102399^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960270409 5000000000 748259102399 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326093333/625000000 : ℝ)^4599 ≤ (43304547750011/100000000000000 : ℝ)^3575 := by
    have hnat : (326093333 : ℕ)^4599*100000000000000^3575 ≤ 43304547750011^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326093333 625000000 43304547750011 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534989197/1000000000 : ℝ), (-960270409/5000000000 : ℝ), (326093333/625000000 : ℝ)] ![(11180826651187/25000000000000 : ℝ), (748259102399/6250000000000 : ℝ), (43304547750011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534989197/1000000000 : ℝ)|^4599 ≤ (11180826651187/25000000000000 : ℝ)^3575
        have hw : |(534989197/1000000000 : ℝ)|=(534989197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960270409/5000000000 : ℝ)|^4599 ≤ (748259102399/6250000000000 : ℝ)^3575
        have hw : |(-960270409/5000000000 : ℝ)|=(960270409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326093333/625000000 : ℝ)|^4599 ≤ (43304547750011/100000000000000 : ℝ)^3575
        have hw : |(326093333/625000000 : ℝ)|=(326093333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337473/2500000 : ℝ)*x 0 + (5217493307/10000000000 : ℝ)*x 1 + (-384108161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337473/2500000 : ℝ)^4599 ≤ (44723306927373/100000000000000 : ℝ)^3575 := by
    have hnat : (1337473 : ℕ)^4599*100000000000000^3575 ≤ 44723306927373^3575*2500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337473 2500000 44723306927373 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217493307/10000000000 : ℝ)^4599 ≤ (43304547525789/100000000000000 : ℝ)^3575 := by
    have hnat : (5217493307 : ℕ)^4599*100000000000000^3575 ≤ 43304547525789^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217493307 10000000000 43304547525789 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384108161/2000000000 : ℝ)^4599 ≤ (11972145534133/100000000000000 : ℝ)^3575 := by
    have hnat : (384108161 : ℕ)^4599*100000000000000^3575 ≤ 11972145534133^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384108161 2000000000 11972145534133 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337473/2500000 : ℝ), (5217493307/10000000000 : ℝ), (-384108161/2000000000 : ℝ)] ![(44723306927373/100000000000000 : ℝ), (43304547525789/100000000000000 : ℝ), (11972145534133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337473/2500000 : ℝ)|^4599 ≤ (44723306927373/100000000000000 : ℝ)^3575
        have hw : |(1337473/2500000 : ℝ)|=(1337473/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217493307/10000000000 : ℝ)|^4599 ≤ (43304547525789/100000000000000 : ℝ)^3575
        have hw : |(5217493307/10000000000 : ℝ)|=(5217493307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384108161/2000000000 : ℝ)|^4599 ≤ (11972145534133/100000000000000 : ℝ)^3575
        have hw : |(-384108161/2000000000 : ℝ)|=(384108161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170070081/400000000 : ℝ)*x 0 + (2004888989/5000000000 : ℝ)*x 1 + (4505612767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170070081/400000000 : ℝ)^4599 ≤ (6655907988119/20000000000000 : ℝ)^3575 := by
    have hnat : (170070081 : ℕ)^4599*20000000000000^3575 ≤ 6655907988119^3575*400000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170070081 400000000 6655907988119 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004888989/5000000000 : ℝ)^4599 ≤ (1234527183589/4000000000000 : ℝ)^3575 := by
    have hnat : (2004888989 : ℕ)^4599*4000000000000^3575 ≤ 1234527183589^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004888989 5000000000 1234527183589 4000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505612767/10000000000 : ℝ)^4599 ≤ (8964320114557/25000000000000 : ℝ)^3575 := by
    have hnat : (4505612767 : ℕ)^4599*25000000000000^3575 ≤ 8964320114557^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505612767 10000000000 8964320114557 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170070081/400000000 : ℝ), (2004888989/5000000000 : ℝ), (4505612767/10000000000 : ℝ)] ![(6655907988119/20000000000000 : ℝ), (1234527183589/4000000000000 : ℝ), (8964320114557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170070081/400000000 : ℝ)|^4599 ≤ (6655907988119/20000000000000 : ℝ)^3575
        have hw : |(170070081/400000000 : ℝ)|=(170070081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004888989/5000000000 : ℝ)|^4599 ≤ (1234527183589/4000000000000 : ℝ)^3575
        have hw : |(2004888989/5000000000 : ℝ)|=(2004888989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505612767/10000000000 : ℝ)|^4599 ≤ (8964320114557/25000000000000 : ℝ)^3575
        have hw : |(4505612767/10000000000 : ℝ)|=(4505612767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905809323/5000000000 : ℝ)*x 0 + (521861817/1000000000 : ℝ)*x 1 + (2714580537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905809323/5000000000 : ℝ)^4599 ≤ (11105860251273/100000000000000 : ℝ)^3575 := by
    have hnat : (905809323 : ℕ)^4599*100000000000000^3575 ≤ 11105860251273^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905809323 5000000000 11105860251273 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521861817/1000000000 : ℝ)^4599 ≤ (21658279163907/50000000000000 : ℝ)^3575 := by
    have hnat : (521861817 : ℕ)^4599*50000000000000^3575 ≤ 21658279163907^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521861817 1000000000 21658279163907 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714580537/5000000000 : ℝ)^4599 ≤ (11394395352163/25000000000000 : ℝ)^3575 := by
    have hnat : (2714580537 : ℕ)^4599*25000000000000^3575 ≤ 11394395352163^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714580537 5000000000 11394395352163 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905809323/5000000000 : ℝ), (521861817/1000000000 : ℝ), (2714580537/5000000000 : ℝ)] ![(11105860251273/100000000000000 : ℝ), (21658279163907/50000000000000 : ℝ), (11394395352163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905809323/5000000000 : ℝ)|^4599 ≤ (11105860251273/100000000000000 : ℝ)^3575
        have hw : |(-905809323/5000000000 : ℝ)|=(905809323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521861817/1000000000 : ℝ)|^4599 ≤ (21658279163907/50000000000000 : ℝ)^3575
        have hw : |(521861817/1000000000 : ℝ)|=(521861817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714580537/5000000000 : ℝ)|^4599 ≤ (11394395352163/25000000000000 : ℝ)^3575
        have hw : |(2714580537/5000000000 : ℝ)|=(2714580537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293722969/10000000000 : ℝ)*x 0 + (-854436491/5000000000 : ℝ)*x 1 + (5429161157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293722969/10000000000 : ℝ)^4599 ≤ (8824033413341/20000000000000 : ℝ)^3575 := by
    have hnat : (5293722969 : ℕ)^4599*20000000000000^3575 ≤ 8824033413341^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293722969 10000000000 8824033413341 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854436491/5000000000 : ℝ)^4599 ≤ (10302250610621/100000000000000 : ℝ)^3575 := by
    have hnat : (854436491 : ℕ)^4599*100000000000000^3575 ≤ 10302250610621^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854436491 5000000000 10302250610621 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429161157/10000000000 : ℝ)^4599 ≤ (9115516461003/20000000000000 : ℝ)^3575 := by
    have hnat : (5429161157 : ℕ)^4599*20000000000000^3575 ≤ 9115516461003^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429161157 10000000000 9115516461003 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293722969/10000000000 : ℝ), (-854436491/5000000000 : ℝ), (5429161157/10000000000 : ℝ)] ![(8824033413341/20000000000000 : ℝ), (10302250610621/100000000000000 : ℝ), (9115516461003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293722969/10000000000 : ℝ)|^4599 ≤ (8824033413341/20000000000000 : ℝ)^3575
        have hw : |(5293722969/10000000000 : ℝ)|=(5293722969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854436491/5000000000 : ℝ)|^4599 ≤ (10302250610621/100000000000000 : ℝ)^3575
        have hw : |(-854436491/5000000000 : ℝ)|=(854436491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429161157/10000000000 : ℝ)|^4599 ≤ (9115516461003/20000000000000 : ℝ)^3575
        have hw : |(5429161157/10000000000 : ℝ)|=(5429161157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058744579/2000000000 : ℝ)*x 0 + (2714580573/5000000000 : ℝ)*x 1 + (-1708873099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058744579/2000000000 : ℝ)^4599 ≤ (441201662733/1000000000000 : ℝ)^3575 := by
    have hnat : (1058744579 : ℕ)^4599*1000000000000^3575 ≤ 441201662733^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058744579 2000000000 441201662733 1000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714580573/5000000000 : ℝ)^4599 ≤ (2278879109311/5000000000000 : ℝ)^3575 := by
    have hnat : (2714580573 : ℕ)^4599*5000000000000^3575 ≤ 2278879109311^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714580573 5000000000 2278879109311 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1708873099/10000000000 : ℝ)^4599 ≤ (2060450303603/20000000000000 : ℝ)^3575 := by
    have hnat : (1708873099 : ℕ)^4599*20000000000000^3575 ≤ 2060450303603^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708873099 10000000000 2060450303603 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058744579/2000000000 : ℝ), (2714580573/5000000000 : ℝ), (-1708873099/10000000000 : ℝ)] ![(441201662733/1000000000000 : ℝ), (2278879109311/5000000000000 : ℝ), (2060450303603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058744579/2000000000 : ℝ)|^4599 ≤ (441201662733/1000000000000 : ℝ)^3575
        have hw : |(1058744579/2000000000 : ℝ)|=(1058744579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714580573/5000000000 : ℝ)|^4599 ≤ (2278879109311/5000000000000 : ℝ)^3575
        have hw : |(2714580573/5000000000 : ℝ)|=(2714580573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1708873099/10000000000 : ℝ)|^4599 ≤ (2060450303603/20000000000000 : ℝ)^3575
        have hw : |(-1708873099/10000000000 : ℝ)|=(1708873099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s3_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251819729/10000000000 : ℝ)*x 0 + (2251495873/5000000000 : ℝ)*x 1 + (100310467/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251819729/10000000000 : ℝ)^4599 ≤ (16640110835033/50000000000000 : ℝ)^3575 := by
    have hnat : (4251819729 : ℕ)^4599*50000000000000^3575 ≤ 16640110835033^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251819729 10000000000 16640110835033 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251495873/5000000000 : ℝ)^4599 ≤ (1791522447271/5000000000000 : ℝ)^3575 := by
    have hnat : (2251495873 : ℕ)^4599*5000000000000^3575 ≤ 1791522447271^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251495873 5000000000 1791522447271 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100310467/250000000 : ℝ)^4599 ≤ (30889329370403/100000000000000 : ℝ)^3575 := by
    have hnat : (100310467 : ℕ)^4599*100000000000000^3575 ≤ 30889329370403^3575*250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100310467 250000000 30889329370403 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251819729/10000000000 : ℝ), (2251495873/5000000000 : ℝ), (100310467/250000000 : ℝ)] ![(16640110835033/50000000000000 : ℝ), (1791522447271/5000000000000 : ℝ), (30889329370403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251819729/10000000000 : ℝ)|^4599 ≤ (16640110835033/50000000000000 : ℝ)^3575
        have hw : |(4251819729/10000000000 : ℝ)|=(4251819729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251495873/5000000000 : ℝ)|^4599 ≤ (1791522447271/5000000000000 : ℝ)^3575
        have hw : |(2251495873/5000000000 : ℝ)|=(2251495873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100310467/250000000 : ℝ)|^4599 ≤ (30889329370403/100000000000000 : ℝ)^3575
        have hw : |(100310467/250000000 : ℝ)|=(100310467/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5509/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1941/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3173/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3173/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3173/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3173/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3173/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3173/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2677/25000 : ℝ) ^ (4597/1024 : ℝ) ≤ (4406671593783263/100000000000000000000 : ℝ) := by
    have hpowers : (2677/25000 : ℝ)^4597 ≤ (4406671593783263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2677 : ℕ)^4597*100000000000000000000^1024 ≤ 4406671593783263^1024*25000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2677 25000 4406671593783263 100000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2677/25000 : ℝ)) (X := (4406671593783263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3173/20000 : ℝ) ^ (4597/1024 : ℝ) ≤ (1286883910054853/5000000000000000000 : ℝ) := by
    have hpowers : (3173/20000 : ℝ)^4597 ≤ (1286883910054853/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3173 : ℕ)^4597*5000000000000000000^1024 ≤ 1286883910054853^1024*20000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3173 20000 1286883910054853 5000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3173/20000 : ℝ)) (X := (1286883910054853/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004406671593783263/50000000000000000000 : ℝ) ≤ (1250024539249327/1250000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50004406671593783263/50000000000000000000 : ℝ)^1024 ≤ (1250024539249327/1250000000000000 : ℝ)^4597 := by
      have hnat : (50004406671593783263 : ℕ)^1024*1250000000000000^4597 ≤ 1250024539249327^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004406671593783263 50000000000000000000 1250024539249327 1250000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024539249327/1250000000000000 : ℝ)) (X := (50004406671593783263/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030144349794880323/100000000000000000000 : ℝ) ≤ (1250083924838853/1250000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (100030144349794880323/100000000000000000000 : ℝ)^1024 ≤ (1250083924838853/1250000000000000 : ℝ)^4597 := by
      have hnat : (100030144349794880323 : ℕ)^1024*1250000000000000^4597 ≤ 1250083924838853^4597*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030144349794880323 100000000000000000000 1250083924838853 1250000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083924838853/1250000000000000 : ℝ)) (X := (100030144349794880323/100000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501286883910054853/2500000000000000000 : ℝ) ≤ (1250143310428379/1250000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (2501286883910054853/2500000000000000000 : ℝ)^1024 ≤ (1250143310428379/1250000000000000 : ℝ)^4597 := by
      have hnat : (2501286883910054853 : ℕ)^1024*1250000000000000^4597 ≤ 1250143310428379^4597*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501286883910054853 2500000000000000000 1250143310428379 1250000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250143310428379/1250000000000000 : ℝ)) (X := (2501286883910054853/2500000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4406671593783263/100000000000000000000 : ℝ) ≤ ((6445104747123490523/6446250000000000000 : ℝ)+2*(29692794763/32231250000000 : ℝ)*(2677/25000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (6445104747123490523/6446250000000000000 : ℝ)+2*(29692794763/32231250000000 : ℝ)*(2677/25000 : ℝ)=(1250024539249327/1250000000000000 : ℝ) by norm_num, show 1+2*(4406671593783263/100000000000000000000 : ℝ)=(50004406671593783263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1286883910054853/5000000000000000000 : ℝ)+(4406671593783263/100000000000000000000 : ℝ) ≤ ((6445104747123490523/6446250000000000000 : ℝ)+(29692794763/32231250000000 : ℝ)*((3173/20000 : ℝ)+(2677/25000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (6445104747123490523/6446250000000000000 : ℝ)+(29692794763/32231250000000 : ℝ)*((3173/20000 : ℝ)+(2677/25000 : ℝ))=(1250083924838853/1250000000000000 : ℝ) by norm_num, show 1+(1286883910054853/5000000000000000000 : ℝ)+(4406671593783263/100000000000000000000 : ℝ)=(100030144349794880323/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1286883910054853/5000000000000000000 : ℝ) ≤ ((6445104747123490523/6446250000000000000 : ℝ)+2*(29692794763/32231250000000 : ℝ)*(3173/20000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (6445104747123490523/6446250000000000000 : ℝ)+2*(29692794763/32231250000000 : ℝ)*(3173/20000 : ℝ)=(1250143310428379/1250000000000000 : ℝ) by norm_num, show 1+2*(1286883910054853/5000000000000000000 : ℝ)=(2501286883910054853/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6445104747123490523/6446250000000000000 : ℝ)*(X 1 0+X 2 0)+(29692794763/32231250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (3173/20000 : ℝ)) (c := (6445104747123490523/6446250000000000000 : ℝ)) (alpha := (29692794763/32231250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6445104747123490523/6446250000000000000 : ℝ)*(X 0 1+X 2 1)+(29692794763/32231250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (3173/20000 : ℝ)) (c := (6445104747123490523/6446250000000000000 : ℝ)) (alpha := (29692794763/32231250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6445104747123490523/6446250000000000000 : ℝ)*(X 0 2+X 1 2)+(29692794763/32231250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (3173/20000 : ℝ)) (c := (6445104747123490523/6446250000000000000 : ℝ)) (alpha := (29692794763/32231250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1811589533/10000000000 : ℝ)*X 0 0+(2715147203/5000000000 : ℝ)*X 0 1+(2608746679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534989197/1000000000 : ℝ)*X 1 0+(-960270409/5000000000 : ℝ)*X 1 1+(326093333/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337473/2500000 : ℝ)*X 2 0+(5217493307/10000000000 : ℝ)*X 2 1+(-384108161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((170070081/400000000 : ℝ)*X 0 0+(2004888989/5000000000 : ℝ)*X 0 1+(4505612767/10000000000 : ℝ)*X 0 2+(170070081/400000000 : ℝ)*X 1 0+(2004888989/5000000000 : ℝ)*X 1 1+(4505612767/10000000000 : ℝ)*X 1 2+(170070081/400000000 : ℝ)*X 2 0+(2004888989/5000000000 : ℝ)*X 2 1+(4505612767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-905809323/5000000000 : ℝ)*X 0 0+(521861817/1000000000 : ℝ)*X 0 1+(2714580537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293722969/10000000000 : ℝ)*X 1 0+(-854436491/5000000000 : ℝ)*X 1 1+(5429161157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058744579/2000000000 : ℝ)*X 2 0+(2714580573/5000000000 : ℝ)*X 2 1+(-1708873099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251819729/10000000000 : ℝ)*X 0 0+(2251495873/5000000000 : ℝ)*X 0 1+(100310467/250000000 : ℝ)*X 0 2+(4251819729/10000000000 : ℝ)*X 1 0+(2251495873/5000000000 : ℝ)*X 1 1+(100310467/250000000 : ℝ)*X 1 2+(4251819729/10000000000 : ℝ)*X 2 0+(2251495873/5000000000 : ℝ)*X 2 1+(100310467/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78955499961205612434423973/17906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47835237/6250000000000 : ℝ)*(base19) + (758378361/100000000000000 : ℝ)*(base23) + (142679/800000000000 : ℝ)*(lower2) + (47733889/50000000000000 : ℝ)*(upper3) + (10963007/12500000000000 : ℝ)*(upper5) + (1679015058450797/50000000000000 : ℝ)*(major0) + (1679015058450797/50000000000000 : ℝ)*(major1) + (1679015058450797/50000000000000 : ℝ)*(major2) + (2349618354836289/50000000000000 : ℝ)*(sp0) + (1174812015238001/25000000000000 : ℝ)*(sp1) + (939849613587487/20000000000000 : ℝ)*(sp2) + (2016805876205321/100000000000000 : ℝ)*(sp3) + (6058321609/50000000000000 : ℝ)*(sp4) + (5384302661/100000000000000 : ℝ)*(sp7) + (1008405630253991/50000000000000 : ℝ)*(f.failure) + (1174812206578949/25000000000000 : ℝ)*(f.sum) + (8421721289573/1611562500000000000000000000 : ℝ)*base66 + (511847143986753169/322312500000000000000000000000000 : ℝ)*base68 + (1068339210422809331/322312500000000000000000000000000 : ℝ)*base69 + (1207528056193878169/322312500000000000000000000000000 : ℝ)*base72 + (3857346171133/6446250000000000000000000000 : ℝ)*base73 + (611688067160809331/322312500000000000000000000000000 : ℝ)*base75 + (967432787378621831/322312500000000000000000000000000 : ℝ)*base77 + (1054534293371434331/322312500000000000000000000000000 : ℝ)*base79 + (973507276079/3223125000000000000000000000 : ℝ)*base81 + (895163/78125000000000000000 : ℝ)*base89 + (895163/78125000000000000000 : ℝ)*base91 + (895163/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2181226956209643003267119/895312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (458988123/100000000000000 : ℝ)*(base19) + (100512953/25000000000000 : ℝ)*(base23) + (10380883/50000000000000 : ℝ)*(upper2) + (62532181/100000000000000 : ℝ)*(upper3) + (84996171/100000000000000 : ℝ)*(upper5) + (42425358286467/1250000000000 : ℝ)*(major0) + (42425358286467/1250000000000 : ℝ)*(major1) + (42425358286467/1250000000000 : ℝ)*(major2) + (8819752389/100000000000000 : ℝ)*(sp1) + (1202961013/20000000000000 : ℝ)*(sp2) + (2374812744616239/50000000000000 : ℝ)*(sp4) + (2374808105245983/50000000000000 : ℝ)*(sp5) + (2374809536187801/50000000000000 : ℝ)*(sp6) + (203843175539309/10000000000000 : ℝ)*(sp7) + (203843175539309/10000000000000 : ℝ)*(f.failure) + (2374812744616239/50000000000000 : ℝ)*(f.sum) + (2250779702687/859500000000000000000000000 : ℝ)*base65 + (2782229594674253/2685937500000000000000000000000 : ℝ)*base68 + (2383574446469497/2685937500000000000000000000000 : ℝ)*base69 + (1096637356766593/671484375000000000000000000000 : ℝ)*base71 + (3055468954499/859500000000000000000000000 : ℝ)*base73 + (7125438333919939/1342968750000000000000000000000 : ℝ)*base76 + (2720990219674253/2685937500000000000000000000000 : ℝ)*base78 + (63575523111389131/5371875000000000000000000000000 : ℝ)*base80 + (3667284948229/1719000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19237/15625000000000000000 : ℝ)*base89 + (19237/15625000000000000000 : ℝ)*base91 + (19237/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1551_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1551_s4_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-362374159/2000000000 : ℝ)*x 0 + (5428424341/10000000000 : ℝ)*x 1 + (2609588521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362374159/2000000000 : ℝ)^4599 ≤ (5553924405621/50000000000000 : ℝ)^3575 := by
    have hnat : (362374159 : ℕ)^4599*50000000000000^3575 ≤ 5553924405621^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362374159 2000000000 5553924405621 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428424341/10000000000 : ℝ)^4599 ≤ (5696203146723/12500000000000 : ℝ)^3575 := by
    have hnat : (5428424341 : ℕ)^4599*12500000000000^3575 ≤ 5696203146723^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428424341 10000000000 5696203146723 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609588521/5000000000 : ℝ)^4599 ≤ (21661262998887/50000000000000 : ℝ)^3575 := by
    have hnat : (2609588521 : ℕ)^4599*50000000000000^3575 ≤ 21661262998887^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609588521 5000000000 21661262998887 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-362374159/2000000000 : ℝ), (5428424341/10000000000 : ℝ), (2609588521/5000000000 : ℝ)] ![(5553924405621/50000000000000 : ℝ), (5696203146723/12500000000000 : ℝ), (21661262998887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-362374159/2000000000 : ℝ)|^4599 ≤ (5553924405621/50000000000000 : ℝ)^3575
        have hw : |(-362374159/2000000000 : ℝ)|=(362374159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428424341/10000000000 : ℝ)|^4599 ≤ (5696203146723/12500000000000 : ℝ)^3575
        have hw : |(5428424341/10000000000 : ℝ)|=(5428424341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609588521/5000000000 : ℝ)|^4599 ≤ (21661262998887/50000000000000 : ℝ)^3575
        have hw : |(2609588521/5000000000 : ℝ)|=(2609588521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674699139/5000000000 : ℝ)*x 0 + (-239870109/1250000000 : ℝ)*x 1 + (163099281/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674699139/5000000000 : ℝ)^4599 ≤ (44717997435057/100000000000000 : ℝ)^3575 := by
    have hnat : (2674699139 : ℕ)^4599*100000000000000^3575 ≤ 44717997435057^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674699139 5000000000 44717997435057 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239870109/1250000000 : ℝ)^4599 ≤ (11959477089377/100000000000000 : ℝ)^3575 := by
    have hnat : (239870109 : ℕ)^4599*100000000000000^3575 ≤ 11959477089377^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239870109 1250000000 11959477089377 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163099281/312500000 : ℝ)^4599 ≤ (21661262731931/50000000000000 : ℝ)^3575 := by
    have hnat : (163099281 : ℕ)^4599*50000000000000^3575 ≤ 21661262731931^3575*312500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163099281 312500000 21661262731931 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674699139/5000000000 : ℝ), (-239870109/1250000000 : ℝ), (163099281/312500000 : ℝ)] ![(44717997435057/100000000000000 : ℝ), (11959477089377/100000000000000 : ℝ), (21661262731931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674699139/5000000000 : ℝ)|^4599 ≤ (44717997435057/100000000000000 : ℝ)^3575
        have hw : |(2674699139/5000000000 : ℝ)|=(2674699139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239870109/1250000000 : ℝ)|^4599 ≤ (11959477089377/100000000000000 : ℝ)^3575
        have hw : |(-239870109/1250000000 : ℝ)|=(239870109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163099281/312500000 : ℝ)|^4599 ≤ (21661262731931/50000000000000 : ℝ)^3575
        have hw : |(163099281/312500000 : ℝ)|=(163099281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349398307/10000000000 : ℝ)*x 0 + (326198561/625000000 : ℝ)*x 1 + (-383792171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349398307/10000000000 : ℝ)^4599 ≤ (44717997746919/100000000000000 : ℝ)^3575 := by
    have hnat : (5349398307 : ℕ)^4599*100000000000000^3575 ≤ 44717997746919^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349398307 10000000000 44717997746919 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326198561/625000000 : ℝ)^4599 ≤ (43322525293011/100000000000000 : ℝ)^3575 := by
    have hnat : (326198561 : ℕ)^4599*100000000000000^3575 ≤ 43322525293011^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326198561 625000000 43322525293011 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383792171/2000000000 : ℝ)^4599 ≤ (11959476953081/100000000000000 : ℝ)^3575 := by
    have hnat : (383792171 : ℕ)^4599*100000000000000^3575 ≤ 11959476953081^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383792171 2000000000 11959476953081 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349398307/10000000000 : ℝ), (326198561/625000000 : ℝ), (-383792171/2000000000 : ℝ)] ![(44717997746919/100000000000000 : ℝ), (43322525293011/100000000000000 : ℝ), (11959476953081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349398307/10000000000 : ℝ)|^4599 ≤ (44717997746919/100000000000000 : ℝ)^3575
        have hw : |(5349398307/10000000000 : ℝ)|=(5349398307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326198561/625000000 : ℝ)|^4599 ≤ (43322525293011/100000000000000 : ℝ)^3575
        have hw : |(326198561/625000000 : ℝ)|=(326198561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-383792171/2000000000 : ℝ)|^4599 ≤ (11959476953081/100000000000000 : ℝ)^3575
        have hw : |(-383792171/2000000000 : ℝ)|=(383792171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16609097/39062500 : ℝ)*x 0 + (501737277/1250000000 : ℝ)*x 1 + (4501452819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16609097/39062500 : ℝ)^4599 ≤ (33281320263551/100000000000000 : ℝ)^3575 := by
    have hnat : (16609097 : ℕ)^4599*100000000000000^3575 ≤ 33281320263551^3575*39062500^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16609097 39062500 33281320263551 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501737277/1250000000 : ℝ)^4599 ≤ (15451991379527/50000000000000 : ℝ)^3575 := by
    have hnat : (501737277 : ℕ)^4599*50000000000000^3575 ≤ 15451991379527^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501737277 1250000000 15451991379527 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501452819/10000000000 : ℝ)^4599 ≤ (17907348481423/50000000000000 : ℝ)^3575 := by
    have hnat : (4501452819 : ℕ)^4599*50000000000000^3575 ≤ 17907348481423^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501452819 10000000000 17907348481423 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16609097/39062500 : ℝ), (501737277/1250000000 : ℝ), (4501452819/10000000000 : ℝ)] ![(33281320263551/100000000000000 : ℝ), (15451991379527/50000000000000 : ℝ), (17907348481423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16609097/39062500 : ℝ)|^4599 ≤ (33281320263551/100000000000000 : ℝ)^3575
        have hw : |(16609097/39062500 : ℝ)|=(16609097/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501737277/1250000000 : ℝ)|^4599 ≤ (15451991379527/50000000000000 : ℝ)^3575
        have hw : |(501737277/1250000000 : ℝ)|=(501737277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501452819/10000000000 : ℝ)|^4599 ≤ (17907348481423/50000000000000 : ℝ)^3575
        have hw : |(4501452819/10000000000 : ℝ)|=(4501452819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811898417/10000000000 : ℝ)*x 0 + (1044052953/2000000000 : ℝ)*x 1 + (5427328561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811898417/10000000000 : ℝ)^4599 ≤ (444322666221/4000000000000 : ℝ)^3575 := by
    have hnat : (1811898417 : ℕ)^4599*4000000000000^3575 ≤ 444322666221^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811898417 10000000000 444322666221 4000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044052953/2000000000 : ℝ)^4599 ≤ (43334141296379/100000000000000 : ℝ)^3575 := by
    have hnat : (1044052953 : ℕ)^4599*100000000000000^3575 ≤ 43334141296379^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044052953 2000000000 43334141296379 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427328561/10000000000 : ℝ)^4599 ≤ (4555779203811/10000000000000 : ℝ)^3575 := by
    have hnat : (5427328561 : ℕ)^4599*10000000000000^3575 ≤ 4555779203811^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427328561 10000000000 4555779203811 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811898417/10000000000 : ℝ), (1044052953/2000000000 : ℝ), (5427328561/10000000000 : ℝ)] ![(444322666221/4000000000000 : ℝ), (43334141296379/100000000000000 : ℝ), (4555779203811/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811898417/10000000000 : ℝ)|^4599 ≤ (444322666221/4000000000000 : ℝ)^3575
        have hw : |(-1811898417/10000000000 : ℝ)|=(1811898417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044052953/2000000000 : ℝ)|^4599 ≤ (43334141296379/100000000000000 : ℝ)^3575
        have hw : |(1044052953/2000000000 : ℝ)|=(1044052953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427328561/10000000000 : ℝ)|^4599 ≤ (4555779203811/10000000000000 : ℝ)^3575
        have hw : |(5427328561/10000000000 : ℝ)|=(5427328561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647083939/5000000000 : ℝ)*x 0 + (-855404659/5000000000 : ℝ)*x 1 + (5427328593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647083939/5000000000 : ℝ)^4599 ≤ (22062468650553/50000000000000 : ℝ)^3575 := by
    have hnat : (2647083939 : ℕ)^4599*50000000000000^3575 ≤ 22062468650553^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647083939 5000000000 22062468650553 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855404659/5000000000 : ℝ)^4599 ≤ (515863514847/5000000000000 : ℝ)^3575 := by
    have hnat : (855404659 : ℕ)^4599*5000000000000^3575 ≤ 515863514847^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855404659 5000000000 515863514847 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427328593/10000000000 : ℝ)^4599 ≤ (22778896191831/50000000000000 : ℝ)^3575 := by
    have hnat : (5427328593 : ℕ)^4599*50000000000000^3575 ≤ 22778896191831^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427328593 10000000000 22778896191831 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647083939/5000000000 : ℝ), (-855404659/5000000000 : ℝ), (5427328593/10000000000 : ℝ)] ![(22062468650553/50000000000000 : ℝ), (515863514847/5000000000000 : ℝ), (22778896191831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647083939/5000000000 : ℝ)|^4599 ≤ (22062468650553/50000000000000 : ℝ)^3575
        have hw : |(2647083939/5000000000 : ℝ)|=(2647083939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855404659/5000000000 : ℝ)|^4599 ≤ (515863514847/5000000000000 : ℝ)^3575
        have hw : |(-855404659/5000000000 : ℝ)|=(855404659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427328593/10000000000 : ℝ)|^4599 ≤ (22778896191831/50000000000000 : ℝ)^3575
        have hw : |(5427328593/10000000000 : ℝ)|=(5427328593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323541973/2500000000 : ℝ)*x 0 + (169604019/312500000 : ℝ)*x 1 + (-855404639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323541973/2500000000 : ℝ)^4599 ≤ (44124937451213/100000000000000 : ℝ)^3575 := by
    have hnat : (1323541973 : ℕ)^4599*100000000000000^3575 ≤ 44124937451213^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323541973 2500000000 44124937451213 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169604019/312500000 : ℝ)^4599 ≤ (1138944813641/2500000000000 : ℝ)^3575 := by
    have hnat : (169604019 : ℕ)^4599*2500000000000^3575 ≤ 1138944813641^3575*312500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169604019 312500000 1138944813641 2500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855404639/5000000000 : ℝ)^4599 ≤ (10317269986619/100000000000000 : ℝ)^3575 := by
    have hnat : (855404639 : ℕ)^4599*100000000000000^3575 ≤ 10317269986619^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855404639 5000000000 10317269986619 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323541973/2500000000 : ℝ), (169604019/312500000 : ℝ), (-855404639/5000000000 : ℝ)] ![(44124937451213/100000000000000 : ℝ), (1138944813641/2500000000000 : ℝ), (10317269986619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323541973/2500000000 : ℝ)|^4599 ≤ (44124937451213/100000000000000 : ℝ)^3575
        have hw : |(1323541973/2500000000 : ℝ)|=(1323541973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169604019/312500000 : ℝ)|^4599 ≤ (1138944813641/2500000000000 : ℝ)^3575
        have hw : |(169604019/312500000 : ℝ)|=(169604019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-855404639/5000000000 : ℝ)|^4599 ≤ (10317269986619/100000000000000 : ℝ)^3575
        have hw : |(-855404639/5000000000 : ℝ)|=(855404639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s4_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125996589/5000000000 : ℝ)*x 0 + (4498918279/10000000000 : ℝ)*x 1 + (4016451501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125996589/5000000000 : ℝ)^4599 ≤ (8320492047019/25000000000000 : ℝ)^3575 := by
    have hnat : (2125996589 : ℕ)^4599*25000000000000^3575 ≤ 8320492047019^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125996589 5000000000 8320492047019 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498918279/10000000000 : ℝ)^4599 ≤ (17894378777293/50000000000000 : ℝ)^3575 := by
    have hnat : (4498918279 : ℕ)^4599*50000000000000^3575 ≤ 17894378777293^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498918279 10000000000 17894378777293 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016451501/10000000000 : ℝ)^4599 ≤ (6185854848601/20000000000000 : ℝ)^3575 := by
    have hnat : (4016451501 : ℕ)^4599*20000000000000^3575 ≤ 6185854848601^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016451501 10000000000 6185854848601 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125996589/5000000000 : ℝ), (4498918279/10000000000 : ℝ), (4016451501/10000000000 : ℝ)] ![(8320492047019/25000000000000 : ℝ), (17894378777293/50000000000000 : ℝ), (6185854848601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125996589/5000000000 : ℝ)|^4599 ≤ (8320492047019/25000000000000 : ℝ)^3575
        have hw : |(2125996589/5000000000 : ℝ)|=(2125996589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498918279/10000000000 : ℝ)|^4599 ≤ (17894378777293/50000000000000 : ℝ)^3575
        have hw : |(4498918279/10000000000 : ℝ)|=(4498918279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016451501/10000000000 : ℝ)|^4599 ≤ (6185854848601/20000000000000 : ℝ)^3575
        have hw : |(4016451501/10000000000 : ℝ)|=(4016451501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1941/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1941/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1941/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5509/50000 : ℝ) ^ (4597/1024 : ℝ) ≤ (5009015410706401/100000000000000000000 : ℝ) := by
    have hpowers : (5509/50000 : ℝ)^4597 ≤ (5009015410706401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5509 : ℕ)^4597*100000000000000000000^1024 ≤ 5009015410706401^1024*50000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5509 50000 5009015410706401 100000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5509/50000 : ℝ)) (X := (5009015410706401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1941/12500 : ℝ) ^ (4597/1024 : ℝ) ≤ (467454166525583/2000000000000000000 : ℝ) := by
    have hpowers : (1941/12500 : ℝ)^4597 ≤ (467454166525583/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1941 : ℕ)^4597*2000000000000000000^1024 ≤ 467454166525583^1024*12500^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1941 12500 467454166525583 2000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1941/12500 : ℝ)) (X := (467454166525583/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005009015410706401/50000000000000000000 : ℝ) ≤ (625013946682889/625000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50005009015410706401/50000000000000000000 : ℝ)^1024 ≤ (625013946682889/625000000000000 : ℝ)^4597 := by
      have hnat : (50005009015410706401 : ℕ)^1024*625000000000000^4597 ≤ 625013946682889^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005009015410706401 50000000000000000000 625013946682889 625000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625013946682889/625000000000000 : ℝ)) (X := (50005009015410706401/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028381723736985551/100000000000000000000 : ℝ) ≤ (312519754513861/312500000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (100028381723736985551/100000000000000000000 : ℝ)^1024 ≤ (312519754513861/312500000000000 : ℝ)^4597 := by
      have hnat : (100028381723736985551 : ℕ)^1024*312500000000000^4597 ≤ 312519754513861^4597*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028381723736985551 100000000000000000000 312519754513861 312500000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312519754513861/312500000000000 : ℝ)) (X := (100028381723736985551/100000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000467454166525583/1000000000000000000 : ℝ) ≤ (125013014274511/125000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (1000467454166525583/1000000000000000000 : ℝ)^1024 ≤ (125013014274511/125000000000000 : ℝ)^4597 := by
      have hnat : (1000467454166525583 : ℕ)^1024*125000000000000^4597 ≤ 125013014274511^4597*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000467454166525583 1000000000000000000 125013014274511 125000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125013014274511/125000000000000 : ℝ)) (X := (1000467454166525583/1000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5009015410706401/100000000000000000000 : ℝ) ≤ ((1409124803854544701/1409375000000000000 : ℝ)+2*(25562344833/28187500000000 : ℝ)*(5509/50000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (1409124803854544701/1409375000000000000 : ℝ)+2*(25562344833/28187500000000 : ℝ)*(5509/50000 : ℝ)=(625013946682889/625000000000000 : ℝ) by norm_num, show 1+2*(5009015410706401/100000000000000000000 : ℝ)=(50005009015410706401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(467454166525583/2000000000000000000 : ℝ)+(5009015410706401/100000000000000000000 : ℝ) ≤ ((1409124803854544701/1409375000000000000 : ℝ)+(25562344833/28187500000000 : ℝ)*((1941/12500 : ℝ)+(5509/50000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (1409124803854544701/1409375000000000000 : ℝ)+(25562344833/28187500000000 : ℝ)*((1941/12500 : ℝ)+(5509/50000 : ℝ))=(312519754513861/312500000000000 : ℝ) by norm_num, show 1+(467454166525583/2000000000000000000 : ℝ)+(5009015410706401/100000000000000000000 : ℝ)=(100028381723736985551/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(467454166525583/2000000000000000000 : ℝ) ≤ ((1409124803854544701/1409375000000000000 : ℝ)+2*(25562344833/28187500000000 : ℝ)*(1941/12500 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (1409124803854544701/1409375000000000000 : ℝ)+2*(25562344833/28187500000000 : ℝ)*(1941/12500 : ℝ)=(125013014274511/125000000000000 : ℝ) by norm_num, show 1+2*(467454166525583/2000000000000000000 : ℝ)=(1000467454166525583/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1409124803854544701/1409375000000000000 : ℝ)*(X 1 0+X 2 0)+(25562344833/28187500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (1409124803854544701/1409375000000000000 : ℝ)) (alpha := (25562344833/28187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1409124803854544701/1409375000000000000 : ℝ)*(X 0 1+X 2 1)+(25562344833/28187500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (1409124803854544701/1409375000000000000 : ℝ)) (alpha := (25562344833/28187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1409124803854544701/1409375000000000000 : ℝ)*(X 0 2+X 1 2)+(25562344833/28187500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1941/12500 : ℝ)) (c := (1409124803854544701/1409375000000000000 : ℝ)) (alpha := (25562344833/28187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-362374159/2000000000 : ℝ)*X 0 0+(5428424341/10000000000 : ℝ)*X 0 1+(2609588521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674699139/5000000000 : ℝ)*X 1 0+(-239870109/1250000000 : ℝ)*X 1 1+(163099281/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349398307/10000000000 : ℝ)*X 2 0+(326198561/625000000 : ℝ)*X 2 1+(-383792171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16609097/39062500 : ℝ)*X 0 0+(501737277/1250000000 : ℝ)*X 0 1+(4501452819/10000000000 : ℝ)*X 0 2+(16609097/39062500 : ℝ)*X 1 0+(501737277/1250000000 : ℝ)*X 1 1+(4501452819/10000000000 : ℝ)*X 1 2+(16609097/39062500 : ℝ)*X 2 0+(501737277/1250000000 : ℝ)*X 2 1+(4501452819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1811898417/10000000000 : ℝ)*X 0 0+(1044052953/2000000000 : ℝ)*X 0 1+(5427328561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647083939/5000000000 : ℝ)*X 1 0+(-855404659/5000000000 : ℝ)*X 1 1+(5427328593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323541973/2500000000 : ℝ)*X 2 0+(169604019/312500000 : ℝ)*X 2 1+(-855404639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2125996589/5000000000 : ℝ)*X 0 0+(4498918279/10000000000 : ℝ)*X 0 1+(4016451501/10000000000 : ℝ)*X 0 2+(2125996589/5000000000 : ℝ)*X 1 0+(4498918279/10000000000 : ℝ)*X 1 1+(4016451501/10000000000 : ℝ)*X 1 2+(2125996589/5000000000 : ℝ)*X 2 0+(4498918279/10000000000 : ℝ)*X 2 1+(4016451501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18525448177327140474568269/3523437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (176532719/20000000000000 : ℝ)*(base19) + (16354159/2000000000000 : ℝ)*(base23) + (24303317/50000000000000 : ℝ)*(lower2) + (15364149/12500000000000 : ℝ)*(upper3) + (78300193/100000000000000 : ℝ)*(upper5) + (341506286525479/10000000000000 : ℝ)*(major0) + (341506286525479/10000000000000 : ℝ)*(major1) + (341506286525479/10000000000000 : ℝ)*(major2) + (1194761893339071/25000000000000 : ℝ)*(sp0) + (4779059910742521/100000000000000 : ℝ)*(sp1) + (2389529987849083/50000000000000 : ℝ)*(sp2) + (128191130845139/6250000000000 : ℝ)*(sp3) + (13220049831/100000000000000 : ℝ)*(sp4) + (6668322003/100000000000000 : ℝ)*(sp7) + (512766190461057/25000000000000 : ℝ)*(f.failure) + (1194765198351529/25000000000000 : ℝ)*(f.sum) + (1932803411613/2255000000000000000000000000 : ℝ)*base66 + (36942222475661779/14093750000000000000000000000000 : ℝ)*base67 + (130377833213224279/14093750000000000000000000000000 : ℝ)*base69 + (68119317476911779/14093750000000000000000000000000 : ℝ)*base71 + (7545880920317/2255000000000000000000000000 : ℝ)*base73 + (84841082179369471/14093750000000000000000000000000 : ℝ)*base76 + (140533381958213221/14093750000000000000000000000000 : ℝ)*base78 + (64168353159818029/14093750000000000000000000000000 : ℝ)*base79 + (3585137764717/2255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (320051/39062500000000000000 : ℝ)*base89 + (320051/39062500000000000000 : ℝ)*base91 + (320051/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2723750911757575796339817/800781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (421853453/100000000000000 : ℝ)*(base19) + (261624527/50000000000000 : ℝ)*(base23) + (4357071/6250000000000 : ℝ)*(upper3) + (17297147/50000000000000 : ℝ)*(lower4) + (3880667/6250000000000 : ℝ)*(upper5) + (1725527600969183/50000000000000 : ℝ)*(major0) + (1725527600969183/50000000000000 : ℝ)*(major1) + (1725527600969183/50000000000000 : ℝ)*(major2) + (6660566527/100000000000000 : ℝ)*(sp1) + (889213229/10000000000000 : ℝ)*(sp2) + (4829428763053409/100000000000000 : ℝ)*(sp4) + (4829421680633429/100000000000000 : ℝ)*(sp5) + (4716229831711/97656250000 : ℝ)*(sp6) + (1036340763722207/50000000000000 : ℝ)*(sp7) + (1036340763722207/50000000000000 : ℝ)*(f.failure) + (4829428763053409/100000000000000 : ℝ)*(f.sum) + (4835460098709/1025000000000000000000000000 : ℝ)*base65 + (71583584798011997/6406250000000000000000000000000 : ℝ)*base68 + (30903913134261997/6406250000000000000000000000000 : ℝ)*base70 + (14626669677543247/6406250000000000000000000000000 : ℝ)*base72 + (49570115579/256250000000000000000000000 : ℝ)*base74 + (9974487667386997/6406250000000000000000000000000 : ℝ)*base76 + (10636651857230747/6406250000000000000000000000000 : ℝ)*base78 + (44703126022769253/6406250000000000000000000000000 : ℝ)*base79 + (57134590923/128125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (761749/78125000000000000000 : ℝ)*base90 + (761749/78125000000000000000 : ℝ)*base92 + (761749/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1551_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1941/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1551_s5_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811900993/10000000000 : ℝ)*x 0 + (169631967/312500000 : ℝ)*x 1 + (2609679207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811900993/10000000000 : ℝ)^4599 ≤ (11108086971513/100000000000000 : ℝ)^3575 := by
    have hnat : (1811900993 : ℕ)^4599*100000000000000^3575 ≤ 11108086971513^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811900993 10000000000 11108086971513 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169631967/312500000 : ℝ)^4599 ≤ (45567450271647/100000000000000 : ℝ)^3575 := by
    have hnat : (169631967 : ℕ)^4599*100000000000000^3575 ≤ 45567450271647^3575*312500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169631967 312500000 45567450271647 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609679207/5000000000 : ℝ)^4599 ≤ (21662231369303/50000000000000 : ℝ)^3575 := by
    have hnat : (2609679207 : ℕ)^4599*50000000000000^3575 ≤ 21662231369303^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609679207 5000000000 21662231369303 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811900993/10000000000 : ℝ), (169631967/312500000 : ℝ), (2609679207/5000000000 : ℝ)] ![(11108086971513/100000000000000 : ℝ), (45567450271647/100000000000000 : ℝ), (21662231369303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811900993/10000000000 : ℝ)|^4599 ≤ (11108086971513/100000000000000 : ℝ)^3575
        have hw : |(-1811900993/10000000000 : ℝ)|=(1811900993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169631967/312500000 : ℝ)|^4599 ≤ (45567450271647/100000000000000 : ℝ)^3575
        have hw : |(169631967/312500000 : ℝ)|=(169631967/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609679207/5000000000 : ℝ)|^4599 ≤ (21662231369303/50000000000000 : ℝ)^3575
        have hw : |(2609679207/5000000000 : ℝ)|=(2609679207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337336253/2500000000 : ℝ)*x 0 + (-479697663/2500000000 : ℝ)*x 1 + (5219358437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337336253/2500000000 : ℝ)^4599 ≤ (22358712310121/50000000000000 : ℝ)^3575 := by
    have hnat : (1337336253 : ℕ)^4599*50000000000000^3575 ≤ 22358712310121^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337336253 2500000000 22358712310121 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479697663/2500000000 : ℝ)^4599 ≤ (11958112385253/100000000000000 : ℝ)^3575 := by
    have hnat : (479697663 : ℕ)^4599*100000000000000^3575 ≤ 11958112385253^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479697663 2500000000 11958112385253 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219358437/10000000000 : ℝ)^4599 ≤ (2707778936513/6250000000000 : ℝ)^3575 := by
    have hnat : (5219358437 : ℕ)^4599*6250000000000^3575 ≤ 2707778936513^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219358437 10000000000 2707778936513 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337336253/2500000000 : ℝ), (-479697663/2500000000 : ℝ), (5219358437/10000000000 : ℝ)] ![(22358712310121/50000000000000 : ℝ), (11958112385253/100000000000000 : ℝ), (2707778936513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337336253/2500000000 : ℝ)|^4599 ≤ (22358712310121/50000000000000 : ℝ)^3575
        have hw : |(1337336253/2500000000 : ℝ)|=(1337336253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479697663/2500000000 : ℝ)|^4599 ≤ (11958112385253/100000000000000 : ℝ)^3575
        have hw : |(-479697663/2500000000 : ℝ)|=(479697663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219358437/10000000000 : ℝ)|^4599 ≤ (2707778936513/6250000000000 : ℝ)^3575
        have hw : |(5219358437/10000000000 : ℝ)|=(5219358437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674672391/5000000000 : ℝ)*x 0 + (163104961/312500000 : ℝ)*x 1 + (-1918790539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674672391/5000000000 : ℝ)^4599 ≤ (44717422146859/100000000000000 : ℝ)^3575 := by
    have hnat : (2674672391 : ℕ)^4599*100000000000000^3575 ≤ 44717422146859^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674672391 5000000000 44717422146859 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163104961/312500000 : ℝ)^4599 ≤ (21662233173941/50000000000000 : ℝ)^3575 := by
    have hnat : (163104961 : ℕ)^4599*50000000000000^3575 ≤ 21662233173941^3575*312500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163104961 312500000 21662233173941 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918790539/10000000000 : ℝ)^4599 ≤ (1195811147931/10000000000000 : ℝ)^3575 := by
    have hnat : (1918790539 : ℕ)^4599*10000000000000^3575 ≤ 1195811147931^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918790539 10000000000 1195811147931 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674672391/5000000000 : ℝ), (163104961/312500000 : ℝ), (-1918790539/10000000000 : ℝ)] ![(44717422146859/100000000000000 : ℝ), (21662233173941/50000000000000 : ℝ), (1195811147931/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674672391/5000000000 : ℝ)|^4599 ≤ (44717422146859/100000000000000 : ℝ)^3575
        have hw : |(2674672391/5000000000 : ℝ)|=(2674672391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163104961/312500000 : ℝ)|^4599 ≤ (21662233173941/50000000000000 : ℝ)^3575
        have hw : |(163104961/312500000 : ℝ)|=(163104961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918790539/10000000000 : ℝ)|^4599 ≤ (1195811147931/10000000000000 : ℝ)^3575
        have hw : |(-1918790539/10000000000 : ℝ)|=(1918790539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425194769/1000000000 : ℝ)*x 0 + (2007171109/5000000000 : ℝ)*x 1 + (4501004593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425194769/1000000000 : ℝ)^4599 ≤ (33281510151687/100000000000000 : ℝ)^3575 := by
    have hnat : (425194769 : ℕ)^4599*100000000000000^3575 ≤ 33281510151687^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425194769 1000000000 33281510151687 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007171109/5000000000 : ℝ)^4599 ≤ (1545419023797/5000000000000 : ℝ)^3575 := by
    have hnat : (2007171109 : ℕ)^4599*5000000000000^3575 ≤ 1545419023797^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007171109 5000000000 1545419023797 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501004593/10000000000 : ℝ)^4599 ≤ (35810109349653/100000000000000 : ℝ)^3575 := by
    have hnat : (4501004593 : ℕ)^4599*100000000000000^3575 ≤ 35810109349653^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501004593 10000000000 35810109349653 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425194769/1000000000 : ℝ), (2007171109/5000000000 : ℝ), (4501004593/10000000000 : ℝ)] ![(33281510151687/100000000000000 : ℝ), (1545419023797/5000000000000 : ℝ), (35810109349653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425194769/1000000000 : ℝ)|^4599 ≤ (33281510151687/100000000000000 : ℝ)^3575
        have hw : |(425194769/1000000000 : ℝ)|=(425194769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007171109/5000000000 : ℝ)|^4599 ≤ (1545419023797/5000000000000 : ℝ)^3575
        have hw : |(2007171109/5000000000 : ℝ)|=(2007171109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501004593/10000000000 : ℝ)|^4599 ≤ (35810109349653/100000000000000 : ℝ)^3575
        have hw : |(4501004593/10000000000 : ℝ)|=(4501004593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-452982139/2500000000 : ℝ)*x 0 + (1044088447/2000000000 : ℝ)*x 1 + (5427131043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452982139/2500000000 : ℝ)^4599 ≤ (5554152175761/50000000000000 : ℝ)^3575 := by
    have hnat : (452982139 : ℕ)^4599*50000000000000^3575 ≤ 5554152175761^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452982139 2500000000 5554152175761 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044088447/2000000000 : ℝ)^4599 ≤ (43336036483481/100000000000000 : ℝ)^3575 := by
    have hnat : (1044088447 : ℕ)^4599*100000000000000^3575 ≤ 43336036483481^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044088447 2000000000 43336036483481 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427131043/10000000000 : ℝ)^4599 ≤ (45555659148723/100000000000000 : ℝ)^3575 := by
    have hnat : (5427131043 : ℕ)^4599*100000000000000^3575 ≤ 45555659148723^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427131043 10000000000 45555659148723 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452982139/2500000000 : ℝ), (1044088447/2000000000 : ℝ), (5427131043/10000000000 : ℝ)] ![(5554152175761/50000000000000 : ℝ), (43336036483481/100000000000000 : ℝ), (45555659148723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452982139/2500000000 : ℝ)|^4599 ≤ (5554152175761/50000000000000 : ℝ)^3575
        have hw : |(-452982139/2500000000 : ℝ)|=(452982139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044088447/2000000000 : ℝ)|^4599 ≤ (43336036483481/100000000000000 : ℝ)^3575
        have hw : |(1044088447/2000000000 : ℝ)|=(1044088447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427131043/10000000000 : ℝ)|^4599 ≤ (45555659148723/100000000000000 : ℝ)^3575
        have hw : |(5427131043/10000000000 : ℝ)|=(5427131043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294215817/10000000000 : ℝ)*x 0 + (-427754509/2500000000 : ℝ)*x 1 + (5427131041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294215817/10000000000 : ℝ)^4599 ≤ (11031362825327/25000000000000 : ℝ)^3575 := by
    have hnat : (5294215817 : ℕ)^4599*25000000000000^3575 ≤ 11031362825327^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294215817 10000000000 11031362825327 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427754509/2500000000 : ℝ)^4599 ≤ (515944478121/5000000000000 : ℝ)^3575 := by
    have hnat : (427754509 : ℕ)^4599*5000000000000^3575 ≤ 515944478121^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427754509 2500000000 515944478121 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427131041/10000000000 : ℝ)^4599 ≤ (22777829563563/50000000000000 : ℝ)^3575 := by
    have hnat : (5427131041 : ℕ)^4599*50000000000000^3575 ≤ 22777829563563^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427131041 10000000000 22777829563563 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294215817/10000000000 : ℝ), (-427754509/2500000000 : ℝ), (5427131041/10000000000 : ℝ)] ![(11031362825327/25000000000000 : ℝ), (515944478121/5000000000000 : ℝ), (22777829563563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294215817/10000000000 : ℝ)|^4599 ≤ (11031362825327/25000000000000 : ℝ)^3575
        have hw : |(5294215817/10000000000 : ℝ)|=(5294215817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427754509/2500000000 : ℝ)|^4599 ≤ (515944478121/5000000000000 : ℝ)^3575
        have hw : |(-427754509/2500000000 : ℝ)|=(427754509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427131041/10000000000 : ℝ)|^4599 ≤ (22777829563563/50000000000000 : ℝ)^3575
        have hw : |(5427131041/10000000000 : ℝ)|=(5427131041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661776977/1250000000 : ℝ)*x 0 + (5427131041/10000000000 : ℝ)*x 1 + (-427754509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661776977/1250000000 : ℝ)^4599 ≤ (22062725645293/50000000000000 : ℝ)^3575 := by
    have hnat : (661776977 : ℕ)^4599*50000000000000^3575 ≤ 22062725645293^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661776977 1250000000 22062725645293 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427131041/10000000000 : ℝ)^4599 ≤ (22777829563563/50000000000000 : ℝ)^3575 := by
    have hnat : (5427131041 : ℕ)^4599*50000000000000^3575 ≤ 22777829563563^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427131041 10000000000 22777829563563 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427754509/2500000000 : ℝ)^4599 ≤ (515944478121/5000000000000 : ℝ)^3575 := by
    have hnat : (427754509 : ℕ)^4599*5000000000000^3575 ≤ 515944478121^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427754509 2500000000 515944478121 5000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661776977/1250000000 : ℝ), (5427131041/10000000000 : ℝ), (-427754509/2500000000 : ℝ)] ![(22062725645293/50000000000000 : ℝ), (22777829563563/50000000000000 : ℝ), (515944478121/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661776977/1250000000 : ℝ)|^4599 ≤ (22062725645293/50000000000000 : ℝ)^3575
        have hw : |(661776977/1250000000 : ℝ)|=(661776977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427131041/10000000000 : ℝ)|^4599 ≤ (22777829563563/50000000000000 : ℝ)^3575
        have hw : |(5427131041/10000000000 : ℝ)|=(5427131041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427754509/2500000000 : ℝ)|^4599 ≤ (515944478121/5000000000000 : ℝ)^3575
        have hw : |(-427754509/2500000000 : ℝ)|=(427754509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s5_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063002923/2500000000 : ℝ)*x 0 + (899695843/2000000000 : ℝ)*x 1 + (2008443117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063002923/2500000000 : ℝ)^4599 ≤ (6656430922631/20000000000000 : ℝ)^3575 := by
    have hnat : (1063002923 : ℕ)^4599*20000000000000^3575 ≤ 6656430922631^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063002923 2500000000 6656430922631 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899695843/2000000000 : ℝ)^4599 ≤ (17892132219247/50000000000000 : ℝ)^3575 := by
    have hnat : (899695843 : ℕ)^4599*50000000000000^3575 ≤ 17892132219247^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899695843 2000000000 17892132219247 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008443117/5000000000 : ℝ)^4599 ≤ (30933580935919/100000000000000 : ℝ)^3575 := by
    have hnat : (2008443117 : ℕ)^4599*100000000000000^3575 ≤ 30933580935919^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008443117 5000000000 30933580935919 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063002923/2500000000 : ℝ), (899695843/2000000000 : ℝ), (2008443117/5000000000 : ℝ)] ![(6656430922631/20000000000000 : ℝ), (17892132219247/50000000000000 : ℝ), (30933580935919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063002923/2500000000 : ℝ)|^4599 ≤ (6656430922631/20000000000000 : ℝ)^3575
        have hw : |(1063002923/2500000000 : ℝ)|=(1063002923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899695843/2000000000 : ℝ)|^4599 ≤ (17892132219247/50000000000000 : ℝ)^3575
        have hw : |(899695843/2000000000 : ℝ)|=(899695843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008443117/5000000000 : ℝ)|^4599 ≤ (30933580935919/100000000000000 : ℝ)^3575
        have hw : |(2008443117/5000000000 : ℝ)|=(2008443117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5527/50000 : ℝ) ^ (4597/1024 : ℝ) ≤ (5082908179139819/100000000000000000000 : ℝ) := by
    have hpowers : (5527/50000 : ℝ)^4597 ≤ (5082908179139819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5527 : ℕ)^4597*100000000000000000000^1024 ≤ 5082908179139819^1024*50000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5527 50000 5082908179139819 100000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5527/50000 : ℝ)) (X := (5082908179139819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4597/1024 : ℝ) ≤ (23110329080421149/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4597 ≤ (23110329080421149/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4597*100000000000000000000^1024 ≤ 23110329080421149^1024*100000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 23110329080421149 100000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (23110329080421149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005082908179139819/50000000000000000000 : ℝ) ≤ (10000226438649531/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50005082908179139819/50000000000000000000 : ℝ)^1024 ≤ (10000226438649531/10000000000000000 : ℝ)^4597 := by
      have hnat : (50005082908179139819 : ℕ)^1024*10000000000000000^4597 ≤ 10000226438649531^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005082908179139819 50000000000000000000 10000226438649531 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000226438649531/10000000000000000 : ℝ)) (X := (50005082908179139819/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503524154657445121/12500000000000000000 : ℝ) ≤ (10000627946755327/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (12503524154657445121/12500000000000000000 : ℝ)^1024 ≤ (10000627946755327/10000000000000000 : ℝ)^4597 := by
      have hnat : (12503524154657445121 : ℕ)^1024*10000000000000000^4597 ≤ 10000627946755327^4597*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503524154657445121 12500000000000000000 10000627946755327 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000627946755327/10000000000000000 : ℝ)) (X := (12503524154657445121/12500000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023110329080421149/50000000000000000000 : ℝ) ≤ (10001029454861123/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50023110329080421149/50000000000000000000 : ℝ)^1024 ≤ (10001029454861123/10000000000000000 : ℝ)^4597 := by
      have hnat : (50023110329080421149 : ℕ)^1024*10000000000000000^4597 ≤ 10001029454861123^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023110329080421149 50000000000000000000 10001029454861123 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001029454861123/10000000000000000 : ℝ)) (X := (50023110329080421149/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5082908179139819/100000000000000000000 : ℝ) ≤ ((44342127714207732017/44350000000000000000 : ℝ)+2*(100377026449/110875000000000 : ℝ)*(5527/50000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (44342127714207732017/44350000000000000000 : ℝ)+2*(100377026449/110875000000000 : ℝ)*(5527/50000 : ℝ)=(10000226438649531/10000000000000000 : ℝ) by norm_num, show 1+2*(5082908179139819/100000000000000000000 : ℝ)=(50005082908179139819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23110329080421149/100000000000000000000 : ℝ)+(5082908179139819/100000000000000000000 : ℝ) ≤ ((44342127714207732017/44350000000000000000 : ℝ)+(100377026449/110875000000000 : ℝ)*((15489/100000 : ℝ)+(5527/50000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (44342127714207732017/44350000000000000000 : ℝ)+(100377026449/110875000000000 : ℝ)*((15489/100000 : ℝ)+(5527/50000 : ℝ))=(10000627946755327/10000000000000000 : ℝ) by norm_num, show 1+(23110329080421149/100000000000000000000 : ℝ)+(5082908179139819/100000000000000000000 : ℝ)=(12503524154657445121/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23110329080421149/100000000000000000000 : ℝ) ≤ ((44342127714207732017/44350000000000000000 : ℝ)+2*(100377026449/110875000000000 : ℝ)*(15489/100000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (44342127714207732017/44350000000000000000 : ℝ)+2*(100377026449/110875000000000 : ℝ)*(15489/100000 : ℝ)=(10001029454861123/10000000000000000 : ℝ) by norm_num, show 1+2*(23110329080421149/100000000000000000000 : ℝ)=(50023110329080421149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44342127714207732017/44350000000000000000 : ℝ)*(X 1 0+X 2 0)+(100377026449/110875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44342127714207732017/44350000000000000000 : ℝ)) (alpha := (100377026449/110875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44342127714207732017/44350000000000000000 : ℝ)*(X 0 1+X 2 1)+(100377026449/110875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44342127714207732017/44350000000000000000 : ℝ)) (alpha := (100377026449/110875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44342127714207732017/44350000000000000000 : ℝ)*(X 0 2+X 1 2)+(100377026449/110875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44342127714207732017/44350000000000000000 : ℝ)) (alpha := (100377026449/110875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1811900993/10000000000 : ℝ)*X 0 0+(169631967/312500000 : ℝ)*X 0 1+(2609679207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337336253/2500000000 : ℝ)*X 1 0+(-479697663/2500000000 : ℝ)*X 1 1+(5219358437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674672391/5000000000 : ℝ)*X 2 0+(163104961/312500000 : ℝ)*X 2 1+(-1918790539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((425194769/1000000000 : ℝ)*X 0 0+(2007171109/5000000000 : ℝ)*X 0 1+(4501004593/10000000000 : ℝ)*X 0 2+(425194769/1000000000 : ℝ)*X 1 0+(2007171109/5000000000 : ℝ)*X 1 1+(4501004593/10000000000 : ℝ)*X 1 2+(425194769/1000000000 : ℝ)*X 2 0+(2007171109/5000000000 : ℝ)*X 2 1+(4501004593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-452982139/2500000000 : ℝ)*X 0 0+(1044088447/2000000000 : ℝ)*X 0 1+(5427131043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294215817/10000000000 : ℝ)*X 1 0+(-427754509/2500000000 : ℝ)*X 1 1+(5427131041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661776977/1250000000 : ℝ)*X 2 0+(5427131041/10000000000 : ℝ)*X 2 1+(-427754509/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1063002923/2500000000 : ℝ)*X 0 0+(899695843/2000000000 : ℝ)*X 0 1+(2008443117/5000000000 : ℝ)*X 0 2+(1063002923/2500000000 : ℝ)*X 1 0+(899695843/2000000000 : ℝ)*X 1 1+(2008443117/5000000000 : ℝ)*X 1 2+(1063002923/2500000000 : ℝ)*X 2 0+(899695843/2000000000 : ℝ)*X 2 1+(2008443117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2601249955396261202527354581/554375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (647706577/100000000000000 : ℝ)*(base19) + (150466709/50000000000000 : ℝ)*(base23) + (75381177/100000000000000 : ℝ)*(lower2) + (10283743/12500000000000 : ℝ)*(upper3) + (14927037/25000000000000 : ℝ)*(upper5) + (1710659449572969/50000000000000 : ℝ)*(major0) + (1710659449572969/50000000000000 : ℝ)*(major1) + (1710659449572969/50000000000000 : ℝ)*(major2) + (2393902036453251/50000000000000 : ℝ)*(sp0) + (957562979734249/20000000000000 : ℝ)*(sp1) + (1196953811361101/25000000000000 : ℝ)*(sp2) + (1027408619438479/50000000000000 : ℝ)*(sp3) + (286836783/2500000000000 : ℝ)*(sp4) + (4856629729/100000000000000 : ℝ)*(sp7) + (2054822095506687/100000000000000 : ℝ)*(f.failure) + (2393907773188911/50000000000000 : ℝ)*(f.sum) + (19844881969149/11087500000000000000000000000 : ℝ)*base65 + (3326307174898948473/2217500000000000000000000000000000 : ℝ)*base67 + (14063141479681448473/2217500000000000000000000000000000 : ℝ)*base69 + (10162126112618551527/2217500000000000000000000000000000 : ℝ)*base72 + (95636274276823/22175000000000000000000000000 : ℝ)*base73 + (13422617764433948473/2217500000000000000000000000000000 : ℝ)*base75 + (7711101313991448473/2217500000000000000000000000000000 : ℝ)*base77 + (16111432660798948473/2217500000000000000000000000000000 : ℝ)*base79 + (19517137491737/5543750000000000000000000000 : ℝ)*base81 + (227391/156250000000000000000 : ℝ)*base89 + (227391/156250000000000000000 : ℝ)*base91 + (227391/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12108215211214071436817551743/2217500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (866053263/100000000000000 : ℝ)*(base19) + (235254667/25000000000000 : ℝ)*(base23) + (283338559/100000000000000 : ℝ)*(lower1) + (55864303/50000000000000 : ℝ)*(upper3) + (6930913/20000000000000 : ℝ)*(lower4) + (113724739/100000000000000 : ℝ)*(upper5) + (3457306692869093/100000000000000 : ℝ)*(major0) + (3457306692869093/100000000000000 : ℝ)*(major1) + (3457306692869093/100000000000000 : ℝ)*(major2) + (500424429/50000000000000 : ℝ)*(sp2) + (151193033471689/3125000000000 : ℝ)*(sp4) + (967635241008157/20000000000000 : ℝ)*(sp5) + (2419087564613261/50000000000000 : ℝ)*(sp6) + (259554516579263/12500000000000 : ℝ)*(sp7) + (259554516579263/12500000000000 : ℝ)*(f.failure) + (151193033471689/3125000000000 : ℝ)*(f.sum) + (3905793930243/5543750000000000000000000000 : ℝ)*base66 + (24410406841108650581/4435000000000000000000000000000000 : ℝ)*base67 + (3338016679491349419/4435000000000000000000000000000000 : ℝ)*base70 + (879857268166353650581/4435000000000000000000000000000000 : ℝ)*base71 + (4809256136941/2771875000000000000000000000 : ℝ)*base73 + (354018678341126349419/4435000000000000000000000000000000 : ℝ)*base76 + (23352366620551349419/4435000000000000000000000000000000 : ℝ)*base78 + (39727930452921349419/4435000000000000000000000000000000 : ℝ)*base80 + (39725959709839/11087500000000000000000000000 : ℝ)*base81 + (321207/39062500000000000000 : ℝ)*base90 + (321207/39062500000000000000 : ℝ)*base92 + (321207/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1551_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1551_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1551_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1551_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1551_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
