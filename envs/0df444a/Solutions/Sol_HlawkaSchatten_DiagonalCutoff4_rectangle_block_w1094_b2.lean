-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:00.711758+00:00
-- url     : https://prove2.me/submissions/52a25f68-14e3-485b-b3be-22d45b07d96b

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
theorem support_rectangle_w1094_s6_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190013687/10000000000 : ℝ)*x 0 + (2697171683/5000000000 : ℝ)*x 1 + (164515779/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190013687/10000000000 : ℝ)^8287 ≤ (13302810360179/100000000000000 : ℝ)^6239 := by
    have hnat : (2190013687 : ℕ)^8287*100000000000000^6239 ≤ 13302810360179^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190013687 10000000000 13302810360179 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697171683/5000000000 : ℝ)^8287 ≤ (550624293203/1250000000000 : ℝ)^6239 := by
    have hnat : (2697171683 : ℕ)^8287*1250000000000^6239 ≤ 550624293203^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697171683 5000000000 550624293203 1250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164515779/312500000 : ℝ)^8287 ≤ (852944923393/2000000000000 : ℝ)^6239 := by
    have hnat : (164515779 : ℕ)^8287*2000000000000^6239 ≤ 852944923393^6239*312500000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164515779 312500000 852944923393 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190013687/10000000000 : ℝ), (2697171683/5000000000 : ℝ), (164515779/312500000 : ℝ)] ![(13302810360179/100000000000000 : ℝ), (550624293203/1250000000000 : ℝ), (852944923393/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190013687/10000000000 : ℝ)|^8287 ≤ (13302810360179/100000000000000 : ℝ)^6239
        have hw : |(-2190013687/10000000000 : ℝ)|=(2190013687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697171683/5000000000 : ℝ)|^8287 ≤ (550624293203/1250000000000 : ℝ)^6239
        have hw : |(2697171683/5000000000 : ℝ)|=(2697171683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164515779/312500000 : ℝ)|^8287 ≤ (852944923393/2000000000000 : ℝ)^6239
        have hw : |(164515779/312500000 : ℝ)|=(164515779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336256781/2500000000 : ℝ)*x 0 + (-2255889059/10000000000 : ℝ)*x 1 + (526450481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336256781/2500000000 : ℝ)^8287 ≤ (43515839731751/100000000000000 : ℝ)^6239 := by
    have hnat : (1336256781 : ℕ)^8287*100000000000000^6239 ≤ 43515839731751^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336256781 2500000000 43515839731751 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255889059/10000000000 : ℝ)^8287 ≤ (13836915354827/100000000000000 : ℝ)^6239 := by
    have hnat : (2255889059 : ℕ)^8287*100000000000000^6239 ≤ 13836915354827^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255889059 10000000000 13836915354827 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526450481/1000000000 : ℝ)^8287 ≤ (42647244899959/100000000000000 : ℝ)^6239 := by
    have hnat : (526450481 : ℕ)^8287*100000000000000^6239 ≤ 42647244899959^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526450481 1000000000 42647244899959 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336256781/2500000000 : ℝ), (-2255889059/10000000000 : ℝ), (526450481/1000000000 : ℝ)] ![(43515839731751/100000000000000 : ℝ), (13836915354827/100000000000000 : ℝ), (42647244899959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336256781/2500000000 : ℝ)|^8287 ≤ (43515839731751/100000000000000 : ℝ)^6239
        have hw : |(1336256781/2500000000 : ℝ)|=(1336256781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255889059/10000000000 : ℝ)|^8287 ≤ (13836915354827/100000000000000 : ℝ)^6239
        have hw : |(-2255889059/10000000000 : ℝ)|=(2255889059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526450481/1000000000 : ℝ)|^8287 ≤ (42647244899959/100000000000000 : ℝ)^6239
        have hw : |(526450481/1000000000 : ℝ)|=(526450481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345027179/10000000000 : ℝ)*x 0 + (2632252409/5000000000 : ℝ)*x 1 + (-90235559/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345027179/10000000000 : ℝ)^8287 ≤ (2719740020407/6250000000000 : ℝ)^6239 := by
    have hnat : (5345027179 : ℕ)^8287*6250000000000^6239 ≤ 2719740020407^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345027179 10000000000 2719740020407 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632252409/5000000000 : ℝ)^8287 ≤ (1066181124651/2500000000000 : ℝ)^6239 := by
    have hnat : (2632252409 : ℕ)^8287*2500000000000^6239 ≤ 1066181124651^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632252409 5000000000 1066181124651 2500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90235559/400000000 : ℝ)^8287 ≤ (13836914670469/100000000000000 : ℝ)^6239 := by
    have hnat : (90235559 : ℕ)^8287*100000000000000^6239 ≤ 13836914670469^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90235559 400000000 13836914670469 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345027179/10000000000 : ℝ), (2632252409/5000000000 : ℝ), (-90235559/400000000 : ℝ)] ![(2719740020407/6250000000000 : ℝ), (1066181124651/2500000000000 : ℝ), (13836914670469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345027179/10000000000 : ℝ)|^8287 ≤ (2719740020407/6250000000000 : ℝ)^6239
        have hw : |(5345027179/10000000000 : ℝ)|=(5345027179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632252409/5000000000 : ℝ)|^8287 ≤ (1066181124651/2500000000000 : ℝ)^6239
        have hw : |(2632252409/5000000000 : ℝ)|=(2632252409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90235559/400000000 : ℝ)|^8287 ≤ (13836914670469/100000000000000 : ℝ)^6239
        have hw : |(-90235559/400000000 : ℝ)|=(90235559/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371457103/10000000000 : ℝ)*x 0 + (4245400603/10000000000 : ℝ)*x 1 + (4501281481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371457103/10000000000 : ℝ)^8287 ≤ (33316471435387/100000000000000 : ℝ)^6239 := by
    have hnat : (4371457103 : ℕ)^8287*100000000000000^6239 ≤ 33316471435387^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371457103 10000000000 33316471435387 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245400603/10000000000 : ℝ)^8287 ≤ (32046463188041/100000000000000 : ℝ)^6239 := by
    have hnat : (4245400603 : ℕ)^8287*100000000000000^6239 ≤ 32046463188041^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245400603 10000000000 32046463188041 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501281481/10000000000 : ℝ)^8287 ≤ (34637065363731/100000000000000 : ℝ)^6239 := by
    have hnat : (4501281481 : ℕ)^8287*100000000000000^6239 ≤ 34637065363731^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501281481 10000000000 34637065363731 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371457103/10000000000 : ℝ), (4245400603/10000000000 : ℝ), (4501281481/10000000000 : ℝ)] ![(33316471435387/100000000000000 : ℝ), (32046463188041/100000000000000 : ℝ), (34637065363731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371457103/10000000000 : ℝ)|^8287 ≤ (33316471435387/100000000000000 : ℝ)^6239
        have hw : |(4371457103/10000000000 : ℝ)|=(4371457103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245400603/10000000000 : ℝ)|^8287 ≤ (32046463188041/100000000000000 : ℝ)^6239
        have hw : |(4245400603/10000000000 : ℝ)|=(4245400603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501281481/10000000000 : ℝ)|^8287 ≤ (34637065363731/100000000000000 : ℝ)^6239
        have hw : |(4501281481/10000000000 : ℝ)|=(4501281481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095009419/5000000000 : ℝ)*x 0 + (5264832677/10000000000 : ℝ)*x 1 + (5394014389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095009419/5000000000 : ℝ)^8287 ≤ (1330285191971/10000000000000 : ℝ)^6239 := by
    have hnat : (1095009419 : ℕ)^8287*10000000000000^6239 ≤ 1330285191971^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095009419 5000000000 1330285191971 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264832677/10000000000 : ℝ)^8287 ≤ (42650772813657/100000000000000 : ℝ)^6239 := by
    have hnat : (5264832677 : ℕ)^8287*100000000000000^6239 ≤ 42650772813657^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264832677 10000000000 42650772813657 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394014389/10000000000 : ℝ)^8287 ≤ (44046375247029/100000000000000 : ℝ)^6239 := by
    have hnat : (5394014389 : ℕ)^8287*100000000000000^6239 ≤ 44046375247029^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394014389 10000000000 44046375247029 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095009419/5000000000 : ℝ), (5264832677/10000000000 : ℝ), (5394014389/10000000000 : ℝ)] ![(1330285191971/10000000000000 : ℝ), (42650772813657/100000000000000 : ℝ), (44046375247029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095009419/5000000000 : ℝ)|^8287 ≤ (1330285191971/10000000000000 : ℝ)^6239
        have hw : |(-1095009419/5000000000 : ℝ)|=(1095009419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264832677/10000000000 : ℝ)|^8287 ≤ (42650772813657/100000000000000 : ℝ)^6239
        have hw : |(5264832677/10000000000 : ℝ)|=(5264832677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394014389/10000000000 : ℝ)|^8287 ≤ (44046375247029/100000000000000 : ℝ)^6239
        have hw : |(5394014389/10000000000 : ℝ)|=(5394014389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328062867/2500000000 : ℝ)*x 0 + (-425275891/2000000000 : ℝ)*x 1 + (1348503593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328062867/2500000000 : ℝ)^8287 ≤ (43161766341897/100000000000000 : ℝ)^6239 := by
    have hnat : (1328062867 : ℕ)^8287*100000000000000^6239 ≤ 43161766341897^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328062867 2500000000 43161766341897 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425275891/2000000000 : ℝ)^8287 ≤ (1598982323263/12500000000000 : ℝ)^6239 := by
    have hnat : (425275891 : ℕ)^8287*12500000000000^6239 ≤ 1598982323263^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425275891 2000000000 1598982323263 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348503593/2500000000 : ℝ)^8287 ≤ (22023187531321/50000000000000 : ℝ)^6239 := by
    have hnat : (1348503593 : ℕ)^8287*50000000000000^6239 ≤ 22023187531321^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348503593 2500000000 22023187531321 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328062867/2500000000 : ℝ), (-425275891/2000000000 : ℝ), (1348503593/2500000000 : ℝ)] ![(43161766341897/100000000000000 : ℝ), (1598982323263/12500000000000 : ℝ), (22023187531321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328062867/2500000000 : ℝ)|^8287 ≤ (43161766341897/100000000000000 : ℝ)^6239
        have hw : |(1328062867/2500000000 : ℝ)|=(1328062867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425275891/2000000000 : ℝ)|^8287 ≤ (1598982323263/12500000000000 : ℝ)^6239
        have hw : |(-425275891/2000000000 : ℝ)|=(425275891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348503593/2500000000 : ℝ)|^8287 ≤ (22023187531321/50000000000000 : ℝ)^6239
        have hw : |(1348503593/2500000000 : ℝ)|=(1348503593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312251457/10000000000 : ℝ)*x 0 + (5394014363/10000000000 : ℝ)*x 1 + (-1063189741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312251457/10000000000 : ℝ)^8287 ≤ (8632353244637/20000000000000 : ℝ)^6239 := by
    have hnat : (5312251457 : ℕ)^8287*20000000000000^6239 ≤ 8632353244637^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312251457 10000000000 8632353244637 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394014363/10000000000 : ℝ)^8287 ≤ (1761854998601/4000000000000 : ℝ)^6239 := by
    have hnat : (5394014363 : ℕ)^8287*4000000000000^6239 ≤ 1761854998601^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394014363 10000000000 1761854998601 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063189741/5000000000 : ℝ)^8287 ≤ (1598982350231/12500000000000 : ℝ)^6239 := by
    have hnat : (1063189741 : ℕ)^8287*12500000000000^6239 ≤ 1598982350231^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063189741 5000000000 1598982350231 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312251457/10000000000 : ℝ), (5394014363/10000000000 : ℝ), (-1063189741/5000000000 : ℝ)] ![(8632353244637/20000000000000 : ℝ), (1761854998601/4000000000000 : ℝ), (1598982350231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312251457/10000000000 : ℝ)|^8287 ≤ (8632353244637/20000000000000 : ℝ)^6239
        have hw : |(5312251457/10000000000 : ℝ)|=(5312251457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394014363/10000000000 : ℝ)|^8287 ≤ (1761854998601/4000000000000 : ℝ)^6239
        have hw : |(5394014363/10000000000 : ℝ)|=(5394014363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063189741/5000000000 : ℝ)|^8287 ≤ (1598982350231/12500000000000 : ℝ)^6239
        have hw : |(-1063189741/5000000000 : ℝ)|=(1063189741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s6_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437146703/1000000000 : ℝ)*x 0 + (1125158839/2500000000 : ℝ)*x 1 + (2123024603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437146703/1000000000 : ℝ)^8287 ≤ (33316571927809/100000000000000 : ℝ)^6239 := by
    have hnat : (437146703 : ℕ)^8287*100000000000000^6239 ≤ 33316571927809^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437146703 1000000000 33316571927809 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125158839/2500000000 : ℝ)^8287 ≤ (34630461568723/100000000000000 : ℝ)^6239 := by
    have hnat : (1125158839 : ℕ)^8287*100000000000000^6239 ≤ 34630461568723^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125158839 2500000000 34630461568723 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123024603/5000000000 : ℝ)^8287 ≤ (32052966485577/100000000000000 : ℝ)^6239 := by
    have hnat : (2123024603 : ℕ)^8287*100000000000000^6239 ≤ 32052966485577^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123024603 5000000000 32052966485577 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437146703/1000000000 : ℝ), (1125158839/2500000000 : ℝ), (2123024603/5000000000 : ℝ)] ![(33316571927809/100000000000000 : ℝ), (34630461568723/100000000000000 : ℝ), (32052966485577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437146703/1000000000 : ℝ)|^8287 ≤ (33316571927809/100000000000000 : ℝ)^6239
        have hw : |(437146703/1000000000 : ℝ)|=(437146703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125158839/2500000000 : ℝ)|^8287 ≤ (34630461568723/100000000000000 : ℝ)^6239
        have hw : |(1125158839/2500000000 : ℝ)|=(1125158839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123024603/5000000000 : ℝ)|^8287 ≤ (32052966485577/100000000000000 : ℝ)^6239
        have hw : |(2123024603/5000000000 : ℝ)|=(2123024603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (141/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (14453260127818877/100000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^4143 ≤ (14453260127818877/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11243 : ℕ)^4143*100000000000000000000^1024 ≤ 14453260127818877^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 14453260127818877 100000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (14453260127818877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (17903153528017889/50000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^4143 ≤ (17903153528017889/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14069 : ℕ)^4143*50000000000000000000^1024 ≤ 17903153528017889^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 17903153528017889 50000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (17903153528017889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014453260127818877/50000000000000000000 : ℝ) ≤ (5000357193537273/5000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50014453260127818877/50000000000000000000 : ℝ)^1024 ≤ (5000357193537273/5000000000000000 : ℝ)^4143 := by
      have hnat : (50014453260127818877 : ℕ)^1024*5000000000000000^4143 ≤ 5000357193537273^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014453260127818877 50000000000000000000 5000357193537273 5000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357193537273/5000000000000000 : ℝ)) (X := (50014453260127818877/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010051913436770931/20000000000000000000 : ℝ) ≤ (10001242000073423/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (20010051913436770931/20000000000000000000 : ℝ)^1024 ≤ (10001242000073423/10000000000000000 : ℝ)^4143 := by
      have hnat : (20010051913436770931 : ℕ)^1024*10000000000000000^4143 ≤ 10001242000073423^4143*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010051913436770931 20000000000000000000 10001242000073423 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001242000073423/10000000000000000 : ℝ)) (X := (20010051913436770931/20000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017903153528017889/25000000000000000000 : ℝ) ≤ (100017696130723/100000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (25017903153528017889/25000000000000000000 : ℝ)^1024 ≤ (100017696130723/100000000000000 : ℝ)^4143 := by
      have hnat : (25017903153528017889 : ℕ)^1024*100000000000000^4143 ≤ 100017696130723^4143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017903153528017889 25000000000000000000 100017696130723 100000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100017696130723/100000000000000 : ℝ)) (X := (25017903153528017889/25000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14453260127818877/100000000000000000000 : ℝ) ≤ ((14125077475989959387/14130000000000000000 : ℝ)+2*(527612998877/282600000000000 : ℝ)*(11243/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (14125077475989959387/14130000000000000000 : ℝ)+2*(527612998877/282600000000000 : ℝ)*(11243/100000 : ℝ)=(5000357193537273/5000000000000000 : ℝ) by norm_num, show 1+2*(14453260127818877/100000000000000000000 : ℝ)=(50014453260127818877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17903153528017889/50000000000000000000 : ℝ)+(14453260127818877/100000000000000000000 : ℝ) ≤ ((14125077475989959387/14130000000000000000 : ℝ)+(527612998877/282600000000000 : ℝ)*((14069/100000 : ℝ)+(11243/100000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (14125077475989959387/14130000000000000000 : ℝ)+(527612998877/282600000000000 : ℝ)*((14069/100000 : ℝ)+(11243/100000 : ℝ))=(10001242000073423/10000000000000000 : ℝ) by norm_num, show 1+(17903153528017889/50000000000000000000 : ℝ)+(14453260127818877/100000000000000000000 : ℝ)=(20010051913436770931/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17903153528017889/50000000000000000000 : ℝ) ≤ ((14125077475989959387/14130000000000000000 : ℝ)+2*(527612998877/282600000000000 : ℝ)*(14069/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (14125077475989959387/14130000000000000000 : ℝ)+2*(527612998877/282600000000000 : ℝ)*(14069/100000 : ℝ)=(100017696130723/100000000000000 : ℝ) by norm_num, show 1+2*(17903153528017889/50000000000000000000 : ℝ)=(25017903153528017889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14125077475989959387/14130000000000000000 : ℝ)*(X 1 0+X 2 0)+(527612998877/282600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (14125077475989959387/14130000000000000000 : ℝ)) (alpha := (527612998877/282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14125077475989959387/14130000000000000000 : ℝ)*(X 0 1+X 2 1)+(527612998877/282600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (14125077475989959387/14130000000000000000 : ℝ)) (alpha := (527612998877/282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14125077475989959387/14130000000000000000 : ℝ)*(X 0 2+X 1 2)+(527612998877/282600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (14125077475989959387/14130000000000000000 : ℝ)) (alpha := (527612998877/282600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190013687/10000000000 : ℝ)*X 0 0+(2697171683/5000000000 : ℝ)*X 0 1+(164515779/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336256781/2500000000 : ℝ)*X 1 0+(-2255889059/10000000000 : ℝ)*X 1 1+(526450481/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345027179/10000000000 : ℝ)*X 2 0+(2632252409/5000000000 : ℝ)*X 2 1+(-90235559/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371457103/10000000000 : ℝ)*X 0 0+(4245400603/10000000000 : ℝ)*X 0 1+(4501281481/10000000000 : ℝ)*X 0 2+(4371457103/10000000000 : ℝ)*X 1 0+(4245400603/10000000000 : ℝ)*X 1 1+(4501281481/10000000000 : ℝ)*X 1 2+(4371457103/10000000000 : ℝ)*X 2 0+(4245400603/10000000000 : ℝ)*X 2 1+(4501281481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1095009419/5000000000 : ℝ)*X 0 0+(5264832677/10000000000 : ℝ)*X 0 1+(5394014389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328062867/2500000000 : ℝ)*X 1 0+(-425275891/2000000000 : ℝ)*X 1 1+(1348503593/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312251457/10000000000 : ℝ)*X 2 0+(5394014363/10000000000 : ℝ)*X 2 1+(-1063189741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437146703/1000000000 : ℝ)*X 0 0+(1125158839/2500000000 : ℝ)*X 0 1+(2123024603/5000000000 : ℝ)*X 0 2+(437146703/1000000000 : ℝ)*X 1 0+(1125158839/2500000000 : ℝ)*X 1 1+(2123024603/5000000000 : ℝ)*X 1 2+(437146703/1000000000 : ℝ)*X 2 0+(1125158839/2500000000 : ℝ)*X 2 1+(2123024603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270266527271074459806009219/39250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347580301/20000000000000 : ℝ)*(base19) + (1626704467/100000000000000 : ℝ)*(base23) + (12724487/12500000000000 : ℝ)*(lower2) + (21876427/12500000000000 : ℝ)*(upper3) + (180318953/100000000000000 : ℝ)*(upper5) + (5805038746393789/100000000000000 : ℝ)*(major0) + (5805038746393789/100000000000000 : ℝ)*(major1) + (5805038746393789/100000000000000 : ℝ)*(major2) + (3850959138724771/50000000000000 : ℝ)*(sp0) + (770195955477311/10000000000000 : ℝ)*(sp1) + (1925489916492537/25000000000000 : ℝ)*(sp2) + (3908091504911573/100000000000000 : ℝ)*(sp3) + (43015225073/100000000000000 : ℝ)*(sp4) + (24465675671/100000000000000 : ℝ)*(sp7) + (977028992646811/25000000000000 : ℝ)*(f.failure) + (1540392258534923/20000000000000 : ℝ)*(f.sum) + (92181598489777/14130000000000000000000000000 : ℝ)*base66 + (2021382776307565781/471000000000000000000000000000000 : ℝ)*base67 + (8359481871003565781/471000000000000000000000000000000 : ℝ)*base69 + (2207067649236565781/471000000000000000000000000000000 : ℝ)*base71 + (38706970752697/14130000000000000000000000000 : ℝ)*base74 + (3137155988586565781/471000000000000000000000000000000 : ℝ)*base75 + (546783088055434219/471000000000000000000000000000000 : ℝ)*base78 + (3122286744666565781/471000000000000000000000000000000 : ℝ)*base79 + (23264712481117/14130000000000000000000000000 : ℝ)*base82 + (15250007/2500000000000000000000 : ℝ)*base89 + (15250007/2500000000000000000000 : ℝ)*base91 + (15250007/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4399122163844176988013/1570000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34835559/4000000000000 : ℝ)*(base19) + (43529389/5000000000000 : ℝ)*(base23) + (198689/1250000000000 : ℝ)*(upper2) + (35570831/50000000000000 : ℝ)*(upper3) + (105217349/100000000000000 : ℝ)*(upper5) + (5834488620050127/100000000000000 : ℝ)*(major0) + (5834488620050127/100000000000000 : ℝ)*(major1) + (5834488620050127/100000000000000 : ℝ)*(major2) + (12231868603/50000000000000 : ℝ)*(sp1) + (11081604761/50000000000000 : ℝ)*(sp2) + (967629336218237/12500000000000 : ℝ)*(sp4) + (1935252338779929/25000000000000 : ℝ)*(sp5) + (3870505827974297/50000000000000 : ℝ)*(sp6) + (3927942456954731/100000000000000 : ℝ)*(sp7) + (3927942456954731/100000000000000 : ℝ)*(f.failure) + (967629336218237/12500000000000 : ℝ)*(f.sum) + (10756393816809/1570000000000000000000000000 : ℝ)*base66 + (1009755459337682461/157000000000000000000000000000000 : ℝ)*base67 + (291519934076317539/157000000000000000000000000000000 : ℝ)*base70 + (387717576099682461/157000000000000000000000000000000 : ℝ)*base71 + (6670959087791/1570000000000000000000000000 : ℝ)*base73 + (1495681935952317539/157000000000000000000000000000000 : ℝ)*base76 + (403637982348317539/157000000000000000000000000000000 : ℝ)*base78 + (813397282255682461/157000000000000000000000000000000 : ℝ)*base79 + (5766141353029/1570000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (40603047/10000000000000000000000 : ℝ)*base89 + (40603047/10000000000000000000000 : ℝ)*base91 + (40603047/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s7_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219004959/1000000000 : ℝ)*x 0 + (2696969909/5000000000 : ℝ)*x 1 + (2632442393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219004959/1000000000 : ℝ)^8287 ≤ (831443752191/6250000000000 : ℝ)^6239 := by
    have hnat : (219004959 : ℕ)^8287*6250000000000^6239 ≤ 831443752191^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219004959 1000000000 831443752191 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696969909/5000000000 : ℝ)^8287 ≤ (22022783215817/50000000000000 : ℝ)^6239 := by
    have hnat : (2696969909 : ℕ)^8287*50000000000000^6239 ≤ 22022783215817^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696969909 5000000000 22022783215817 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632442393/5000000000 : ℝ)^8287 ≤ (21325666761717/50000000000000 : ℝ)^6239 := by
    have hnat : (2632442393 : ℕ)^8287*50000000000000^6239 ≤ 21325666761717^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632442393 5000000000 21325666761717 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219004959/1000000000 : ℝ), (2696969909/5000000000 : ℝ), (2632442393/5000000000 : ℝ)] ![(831443752191/6250000000000 : ℝ), (22022783215817/50000000000000 : ℝ), (21325666761717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219004959/1000000000 : ℝ)|^8287 ≤ (831443752191/6250000000000 : ℝ)^6239
        have hw : |(-219004959/1000000000 : ℝ)|=(219004959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696969909/5000000000 : ℝ)|^8287 ≤ (22022783215817/50000000000000 : ℝ)^6239
        have hw : |(2696969909/5000000000 : ℝ)|=(2696969909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632442393/5000000000 : ℝ)|^8287 ≤ (21325666761717/50000000000000 : ℝ)^6239
        have hw : |(2632442393/5000000000 : ℝ)|=(2632442393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344925741/10000000000 : ℝ)*x 0 + (-2255521683/10000000000 : ℝ)*x 1 + (105297697/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344925741/10000000000 : ℝ)^8287 ≤ (8702948679191/20000000000000 : ℝ)^6239 := by
    have hnat : (5344925741 : ℕ)^8287*20000000000000^6239 ≤ 8702948679191^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344925741 10000000000 8702948679191 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255521683/10000000000 : ℝ)^8287 ≤ (6916961189973/50000000000000 : ℝ)^6239 := by
    have hnat : (2255521683 : ℕ)^8287*50000000000000^6239 ≤ 6916961189973^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255521683 10000000000 6916961189973 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105297697/200000000 : ℝ)^8287 ≤ (83303387133/195312500000 : ℝ)^6239 := by
    have hnat : (105297697 : ℕ)^8287*195312500000^6239 ≤ 83303387133^6239*200000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105297697 200000000 83303387133 195312500000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344925741/10000000000 : ℝ), (-2255521683/10000000000 : ℝ), (105297697/200000000 : ℝ)] ![(8702948679191/20000000000000 : ℝ), (6916961189973/50000000000000 : ℝ), (83303387133/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344925741/10000000000 : ℝ)|^8287 ≤ (8702948679191/20000000000000 : ℝ)^6239
        have hw : |(5344925741/10000000000 : ℝ)|=(5344925741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255521683/10000000000 : ℝ)|^8287 ≤ (6916961189973/50000000000000 : ℝ)^6239
        have hw : |(-2255521683/10000000000 : ℝ)|=(2255521683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105297697/200000000 : ℝ)|^8287 ≤ (83303387133/195312500000 : ℝ)^6239
        have hw : |(105297697/200000000 : ℝ)|=(105297697/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344925901/10000000000 : ℝ)*x 0 + (5264884741/10000000000 : ℝ)*x 1 + (-1127760807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344925901/10000000000 : ℝ)^8287 ≤ (21757372563079/50000000000000 : ℝ)^6239 := by
    have hnat : (5344925901 : ℕ)^8287*50000000000000^6239 ≤ 21757372563079^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344925901 10000000000 21757372563079 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264884741/10000000000 : ℝ)^8287 ≤ (42651333039219/100000000000000 : ℝ)^6239 := by
    have hnat : (5264884741 : ℕ)^8287*100000000000000^6239 ≤ 42651333039219^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264884741 10000000000 42651333039219 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127760807/5000000000 : ℝ)^8287 ≤ (553356872713/4000000000000 : ℝ)^6239 := by
    have hnat : (1127760807 : ℕ)^8287*4000000000000^6239 ≤ 553356872713^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127760807 5000000000 553356872713 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344925901/10000000000 : ℝ), (5264884741/10000000000 : ℝ), (-1127760807/5000000000 : ℝ)] ![(21757372563079/50000000000000 : ℝ), (42651333039219/100000000000000 : ℝ), (553356872713/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344925901/10000000000 : ℝ)|^8287 ≤ (21757372563079/50000000000000 : ℝ)^6239
        have hw : |(5344925901/10000000000 : ℝ)|=(5344925901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264884741/10000000000 : ℝ)|^8287 ≤ (42651333039219/100000000000000 : ℝ)^6239
        have hw : |(5264884741/10000000000 : ℝ)|=(5264884741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127760807/5000000000 : ℝ)|^8287 ≤ (553356872713/4000000000000 : ℝ)^6239
        have hw : |(-1127760807/5000000000 : ℝ)|=(1127760807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092869257/2500000000 : ℝ)*x 0 + (4246170299/10000000000 : ℝ)*x 1 + (1125126663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092869257/2500000000 : ℝ)^8287 ≤ (666333462781/2000000000000 : ℝ)^6239 := by
    have hnat : (1092869257 : ℕ)^8287*2000000000000^6239 ≤ 666333462781^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092869257 2500000000 666333462781 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246170299/10000000000 : ℝ)^8287 ≤ (100169314611/312500000000 : ℝ)^6239 := by
    have hnat : (4246170299 : ℕ)^8287*312500000000^6239 ≤ 100169314611^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246170299 10000000000 100169314611 312500000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125126663/2500000000 : ℝ)^8287 ≤ (3462914617183/10000000000000 : ℝ)^6239 := by
    have hnat : (1125126663 : ℕ)^8287*10000000000000^6239 ≤ 3462914617183^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125126663 2500000000 3462914617183 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092869257/2500000000 : ℝ), (4246170299/10000000000 : ℝ), (1125126663/2500000000 : ℝ)] ![(666333462781/2000000000000 : ℝ), (100169314611/312500000000 : ℝ), (3462914617183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092869257/2500000000 : ℝ)|^8287 ≤ (666333462781/2000000000000 : ℝ)^6239
        have hw : |(1092869257/2500000000 : ℝ)|=(1092869257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246170299/10000000000 : ℝ)|^8287 ≤ (100169314611/312500000000 : ℝ)^6239
        have hw : |(4246170299/10000000000 : ℝ)|=(4246170299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125126663/2500000000 : ℝ)|^8287 ≤ (3462914617183/10000000000000 : ℝ)^6239
        have hw : |(1125126663/2500000000 : ℝ)|=(1125126663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190054667/10000000000 : ℝ)*x 0 + (2632604371/5000000000 : ℝ)*x 1 + (5393614643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190054667/10000000000 : ℝ)^8287 ≤ (13303140997757/100000000000000 : ℝ)^6239 := by
    have hnat : (2190054667 : ℕ)^8287*100000000000000^6239 ≤ 13303140997757^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190054667 10000000000 13303140997757 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632604371/5000000000 : ℝ)^8287 ≤ (21327409718079/50000000000000 : ℝ)^6239 := by
    have hnat : (2632604371 : ℕ)^8287*50000000000000^6239 ≤ 21327409718079^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632604371 5000000000 21327409718079 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393614643/10000000000 : ℝ)^8287 ≤ (44042039546563/100000000000000 : ℝ)^6239 := by
    have hnat : (5393614643 : ℕ)^8287*100000000000000^6239 ≤ 44042039546563^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393614643 10000000000 44042039546563 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190054667/10000000000 : ℝ), (2632604371/5000000000 : ℝ), (5393614643/10000000000 : ℝ)] ![(13303140997757/100000000000000 : ℝ), (21327409718079/50000000000000 : ℝ), (44042039546563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190054667/10000000000 : ℝ)|^8287 ≤ (13303140997757/100000000000000 : ℝ)^6239
        have hw : |(-2190054667/10000000000 : ℝ)|=(2190054667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632604371/5000000000 : ℝ)|^8287 ≤ (21327409718079/50000000000000 : ℝ)^6239
        have hw : |(2632604371/5000000000 : ℝ)|=(2632604371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393614643/10000000000 : ℝ)|^8287 ≤ (44042039546563/100000000000000 : ℝ)^6239
        have hw : |(5393614643/10000000000 : ℝ)|=(5393614643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312347839/10000000000 : ℝ)*x 0 + (-2126791867/10000000000 : ℝ)*x 1 + (2696807321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312347839/10000000000 : ℝ)^8287 ≤ (21581403191611/50000000000000 : ℝ)^6239 := by
    have hnat : (5312347839 : ℕ)^8287*50000000000000^6239 ≤ 21581403191611^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312347839 10000000000 21581403191611 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126791867/10000000000 : ℝ)^8287 ≤ (3198788519699/25000000000000 : ℝ)^6239 := by
    have hnat : (2126791867 : ℕ)^8287*25000000000000^6239 ≤ 3198788519699^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126791867 10000000000 3198788519699 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696807321/5000000000 : ℝ)^8287 ≤ (44042039535717/100000000000000 : ℝ)^6239 := by
    have hnat : (2696807321 : ℕ)^8287*100000000000000^6239 ≤ 44042039535717^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696807321 5000000000 44042039535717 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312347839/10000000000 : ℝ), (-2126791867/10000000000 : ℝ), (2696807321/5000000000 : ℝ)] ![(21581403191611/50000000000000 : ℝ), (3198788519699/25000000000000 : ℝ), (44042039535717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312347839/10000000000 : ℝ)|^8287 ≤ (21581403191611/50000000000000 : ℝ)^6239
        have hw : |(5312347839/10000000000 : ℝ)|=(5312347839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126791867/10000000000 : ℝ)|^8287 ≤ (3198788519699/25000000000000 : ℝ)^6239
        have hw : |(-2126791867/10000000000 : ℝ)|=(2126791867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696807321/5000000000 : ℝ)|^8287 ≤ (44042039535717/100000000000000 : ℝ)^6239
        have hw : |(2696807321/5000000000 : ℝ)|=(2696807321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312347841/10000000000 : ℝ)*x 0 + (67420183/125000000 : ℝ)*x 1 + (-425358373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312347841/10000000000 : ℝ)^8287 ≤ (21581403202403/50000000000000 : ℝ)^6239 := by
    have hnat : (5312347841 : ℕ)^8287*50000000000000^6239 ≤ 21581403202403^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312347841 10000000000 21581403202403 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67420183/125000000 : ℝ)^8287 ≤ (1761681580561/4000000000000 : ℝ)^6239 := by
    have hnat : (67420183 : ℕ)^8287*4000000000000^6239 ≤ 1761681580561^6239*125000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67420183 125000000 1761681580561 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425358373/2000000000 : ℝ)^8287 ≤ (6397577031407/50000000000000 : ℝ)^6239 := by
    have hnat : (425358373 : ℕ)^8287*50000000000000^6239 ≤ 6397577031407^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425358373 2000000000 6397577031407 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312347841/10000000000 : ℝ), (67420183/125000000 : ℝ), (-425358373/2000000000 : ℝ)] ![(21581403202403/50000000000000 : ℝ), (1761681580561/4000000000000 : ℝ), (6397577031407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312347841/10000000000 : ℝ)|^8287 ≤ (21581403202403/50000000000000 : ℝ)^6239
        have hw : |(5312347841/10000000000 : ℝ)|=(5312347841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67420183/125000000 : ℝ)|^8287 ≤ (1761681580561/4000000000000 : ℝ)^6239
        have hw : |(67420183/125000000 : ℝ)|=(67420183/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425358373/2000000000 : ℝ)|^8287 ≤ (6397577031407/50000000000000 : ℝ)^6239
        have hw : |(-425358373/2000000000 : ℝ)|=(425358373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s7_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371486851/10000000000 : ℝ)*x 0 + (4499868309/10000000000 : ℝ)*x 1 + (4246811/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371486851/10000000000 : ℝ)^8287 ≤ (16658386289407/50000000000000 : ℝ)^6239 := by
    have hnat : (4371486851 : ℕ)^8287*50000000000000^6239 ≤ 16658386289407^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371486851 10000000000 16658386289407 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499868309/10000000000 : ℝ)^8287 ≤ (34622622280497/100000000000000 : ℝ)^6239 := by
    have hnat : (4499868309 : ℕ)^8287*100000000000000^6239 ≤ 34622622280497^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499868309 10000000000 34622622280497 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246811/10000000 : ℝ)^8287 ≤ (8015151280747/25000000000000 : ℝ)^6239 := by
    have hnat : (4246811 : ℕ)^8287*25000000000000^6239 ≤ 8015151280747^6239*10000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246811 10000000 8015151280747 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371486851/10000000000 : ℝ), (4499868309/10000000000 : ℝ), (4246811/10000000 : ℝ)] ![(16658386289407/50000000000000 : ℝ), (34622622280497/100000000000000 : ℝ), (8015151280747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371486851/10000000000 : ℝ)|^8287 ≤ (16658386289407/50000000000000 : ℝ)^6239
        have hw : |(4371486851/10000000000 : ℝ)|=(4371486851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499868309/10000000000 : ℝ)|^8287 ≤ (34622622280497/100000000000000 : ℝ)^6239
        have hw : |(4499868309/10000000000 : ℝ)|=(4499868309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246811/10000000 : ℝ)|^8287 ≤ (8015151280747/25000000000000 : ℝ)^6239
        have hw : |(4246811/10000000 : ℝ)|=(4246811/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7011/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (141/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (141/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (141/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (141/1250 : ℝ) ^ (4143/1024 : ℝ) ≤ (1830833624910059/12500000000000000000 : ℝ) := by
    have hpowers : (141/1250 : ℝ)^4143 ≤ (1830833624910059/12500000000000000000 : ℝ)^1024 := by
      have hnat : (141 : ℕ)^4143*12500000000000000000^1024 ≤ 1830833624910059^1024*1250^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1250 1830833624910059 12500000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1250 : ℝ)) (X := (1830833624910059/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1403/10000 : ℝ) ^ (4143/1024 : ℝ) ≤ (2212900980814101/6250000000000000000 : ℝ) := by
    have hpowers : (1403/10000 : ℝ)^4143 ≤ (2212900980814101/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1403 : ℕ)^4143*6250000000000000000^1024 ≤ 2212900980814101^1024*10000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 10000 2212900980814101 6250000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/10000 : ℝ)) (X := (2212900980814101/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251830833624910059/6250000000000000000 : ℝ) ≤ (2000144789143681/2000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (6251830833624910059/6250000000000000000 : ℝ)^1024 ≤ (2000144789143681/2000000000000000 : ℝ)^4143 := by
      have hnat : (6251830833624910059 : ℕ)^1024*2000000000000000^4143 ≤ 2000144789143681^4143*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251830833624910059 6250000000000000000 2000144789143681 2000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144789143681/2000000000000000 : ℝ)) (X := (6251830833624910059/6250000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506256635586538261/12500000000000000000 : ℝ) ≤ (10001236898498031/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (12506256635586538261/12500000000000000000 : ℝ)^1024 ≤ (10001236898498031/10000000000000000 : ℝ)^4143 := by
      have hnat : (12506256635586538261 : ℕ)^1024*10000000000000000^4143 ≤ 10001236898498031^4143*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506256635586538261 12500000000000000000 10001236898498031 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001236898498031/10000000000000000 : ℝ)) (X := (12506256635586538261/12500000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127212900980814101/3125000000000000000 : ℝ) ≤ (10001749851277657/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (3127212900980814101/3125000000000000000 : ℝ)^1024 ≤ (10001749851277657/10000000000000000 : ℝ)^4143 := by
      have hnat : (3127212900980814101 : ℕ)^1024*10000000000000000^4143 ≤ 10001749851277657^4143*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127212900980814101 3125000000000000000 10001749851277657 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001749851277657/10000000000000000 : ℝ)) (X := (3127212900980814101/3125000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1830833624910059/12500000000000000000 : ℝ) ≤ ((2749041863601725119/2750000000000000000 : ℝ)+2*(256476389813/137500000000000 : ℝ)*(141/1250 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (2749041863601725119/2750000000000000000 : ℝ)+2*(256476389813/137500000000000 : ℝ)*(141/1250 : ℝ)=(2000144789143681/2000000000000000 : ℝ) by norm_num, show 1+2*(1830833624910059/12500000000000000000 : ℝ)=(6251830833624910059/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2212900980814101/6250000000000000000 : ℝ)+(1830833624910059/12500000000000000000 : ℝ) ≤ ((2749041863601725119/2750000000000000000 : ℝ)+(256476389813/137500000000000 : ℝ)*((1403/10000 : ℝ)+(141/1250 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (2749041863601725119/2750000000000000000 : ℝ)+(256476389813/137500000000000 : ℝ)*((1403/10000 : ℝ)+(141/1250 : ℝ))=(10001236898498031/10000000000000000 : ℝ) by norm_num, show 1+(2212900980814101/6250000000000000000 : ℝ)+(1830833624910059/12500000000000000000 : ℝ)=(12506256635586538261/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2212900980814101/6250000000000000000 : ℝ) ≤ ((2749041863601725119/2750000000000000000 : ℝ)+2*(256476389813/137500000000000 : ℝ)*(1403/10000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (2749041863601725119/2750000000000000000 : ℝ)+2*(256476389813/137500000000000 : ℝ)*(1403/10000 : ℝ)=(10001749851277657/10000000000000000 : ℝ) by norm_num, show 1+2*(2212900980814101/6250000000000000000 : ℝ)=(3127212900980814101/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2749041863601725119/2750000000000000000 : ℝ)*(X 1 0+X 2 0)+(256476389813/137500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (2749041863601725119/2750000000000000000 : ℝ)) (alpha := (256476389813/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2749041863601725119/2750000000000000000 : ℝ)*(X 0 1+X 2 1)+(256476389813/137500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (2749041863601725119/2750000000000000000 : ℝ)) (alpha := (256476389813/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2749041863601725119/2750000000000000000 : ℝ)*(X 0 2+X 1 2)+(256476389813/137500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (141/1250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (2749041863601725119/2750000000000000000 : ℝ)) (alpha := (256476389813/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219004959/1000000000 : ℝ)*X 0 0+(2696969909/5000000000 : ℝ)*X 0 1+(2632442393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344925741/10000000000 : ℝ)*X 1 0+(-2255521683/10000000000 : ℝ)*X 1 1+(105297697/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344925901/10000000000 : ℝ)*X 2 0+(5264884741/10000000000 : ℝ)*X 2 1+(-1127760807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092869257/2500000000 : ℝ)*X 0 0+(4246170299/10000000000 : ℝ)*X 0 1+(1125126663/2500000000 : ℝ)*X 0 2+(1092869257/2500000000 : ℝ)*X 1 0+(4246170299/10000000000 : ℝ)*X 1 1+(1125126663/2500000000 : ℝ)*X 1 2+(1092869257/2500000000 : ℝ)*X 2 0+(4246170299/10000000000 : ℝ)*X 2 1+(1125126663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2190054667/10000000000 : ℝ)*X 0 0+(2632604371/5000000000 : ℝ)*X 0 1+(5393614643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312347839/10000000000 : ℝ)*X 1 0+(-2126791867/10000000000 : ℝ)*X 1 1+(2696807321/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312347841/10000000000 : ℝ)*X 2 0+(67420183/125000000 : ℝ)*X 2 1+(-425358373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371486851/10000000000 : ℝ)*X 0 0+(4499868309/10000000000 : ℝ)*X 0 1+(4246811/10000000 : ℝ)*X 0 2+(4371486851/10000000000 : ℝ)*X 1 0+(4499868309/10000000000 : ℝ)*X 1 1+(4246811/10000000 : ℝ)*X 1 2+(4371486851/10000000000 : ℝ)*X 2 0+(4499868309/10000000000 : ℝ)*X 2 1+(4246811/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1149284913798185680835643129/137500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1724251969/100000000000000 : ℝ)*(base19) + (340865457/20000000000000 : ℝ)*(base23) + (134629339/100000000000000 : ℝ)*(lower2) + (21259023/12500000000000 : ℝ)*(upper3) + (16935223/12500000000000 : ℝ)*(upper5) + (5840293039055597/100000000000000 : ℝ)*(major0) + (5840293039055597/100000000000000 : ℝ)*(major1) + (5840293039055597/100000000000000 : ℝ)*(major2) + (7748681579193693/100000000000000 : ℝ)*(sp0) + (7748733919546459/100000000000000 : ℝ)*(sp1) + (7748733939471143/100000000000000 : ℝ)*(sp2) + (1965912006372413/50000000000000 : ℝ)*(sp3) + (10812920947/20000000000000 : ℝ)*(sp4) + (13071476703/50000000000000 : ℝ)*(sp7) + (491481269462279/12500000000000 : ℝ)*(f.failure) + (7748735643798427/100000000000000 : ℝ)*(f.sum) + (8412864127441/1718750000000000000000000000 : ℝ)*base66 + (202713835852758087/25000000000000000000000000000000 : ℝ)*base68 + (453287584572241913/25000000000000000000000000000000 : ℝ)*base69 + (222217037877758087/25000000000000000000000000000000 : ℝ)*base72 + (1979691794829/429687500000000000000000000 : ℝ)*base74 + (190068836602758087/25000000000000000000000000000000 : ℝ)*base76 + (139923880977758087/25000000000000000000000000000000 : ℝ)*base78 + (200116971172241913/25000000000000000000000000000000 : ℝ)*base79 + (27695363152111/6875000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5706323/1250000000000000000000 : ℝ)*base89 + (5706323/1250000000000000000000 : ℝ)*base91 + (5706323/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54387296401688227482849/6875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22635983/1562500000000 : ℝ)*(base19) + (791616803/50000000000000 : ℝ)*(base23) + (19652189/12500000000000 : ℝ)*(upper3) + (11919289/20000000000000 : ℝ)*(lower4) + (79980787/50000000000000 : ℝ)*(upper5) + (5869738273718559/100000000000000 : ℝ)*(major0) + (5869738273718559/100000000000000 : ℝ)*(major1) + (5869738273718559/100000000000000 : ℝ)*(major2) + (197829923/500000000000 : ℝ)*(sp1) + (42731536687/100000000000000 : ℝ)*(sp2) + (3893901382388359/50000000000000 : ℝ)*(sp4) + (7787761750089207/100000000000000 : ℝ)*(sp5) + (973469806250803/12500000000000 : ℝ)*(sp6) + (987918379741103/25000000000000 : ℝ)*(sp7) + (987918379741103/25000000000000 : ℝ)*(f.failure) + (3893901382388359/50000000000000 : ℝ)*(f.sum) + (2464173660717/6875000000000000000000000000 : ℝ)*base65 + (24114189697829411/25000000000000000000000000000000 : ℝ)*base67 + (24513950552170589/25000000000000000000000000000000 : ℝ)*base70 + (115758830827170589/25000000000000000000000000000000 : ℝ)*base72 + (1866806310671/3437500000000000000000000000 : ℝ)*base73 + (57376118947829411/25000000000000000000000000000000 : ℝ)*base75 + (51691288277170589/25000000000000000000000000000000 : ℝ)*base78 + (170194897922829411/25000000000000000000000000000000 : ℝ)*base79 + (18440190011783/6875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (32834811/2500000000000000000000 : ℝ)*base89 + (32834811/2500000000000000000000 : ℝ)*base91 + (32834811/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s8_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190055719/10000000000 : ℝ)*x 0 + (1078771307/2000000000 : ℝ)*x 1 + (2632482069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190055719/10000000000 : ℝ)^8287 ≤ (13303149485601/100000000000000 : ℝ)^6239 := by
    have hnat : (2190055719 : ℕ)^8287*100000000000000^6239 ≤ 13303149485601^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190055719 10000000000 13303149485601 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078771307/2000000000 : ℝ)^8287 ≤ (22022331564043/50000000000000 : ℝ)^6239 := by
    have hnat : (1078771307 : ℕ)^8287*50000000000000^6239 ≤ 22022331564043^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078771307 2000000000 22022331564043 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632482069/5000000000 : ℝ)^8287 ≤ (8530437476049/20000000000000 : ℝ)^6239 := by
    have hnat : (2632482069 : ℕ)^8287*20000000000000^6239 ≤ 8530437476049^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632482069 5000000000 8530437476049 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190055719/10000000000 : ℝ), (1078771307/2000000000 : ℝ), (2632482069/5000000000 : ℝ)] ![(13303149485601/100000000000000 : ℝ), (22022331564043/50000000000000 : ℝ), (8530437476049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190055719/10000000000 : ℝ)|^8287 ≤ (13303149485601/100000000000000 : ℝ)^6239
        have hw : |(-2190055719/10000000000 : ℝ)|=(2190055719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078771307/2000000000 : ℝ)|^8287 ≤ (22022331564043/50000000000000 : ℝ)^6239
        have hw : |(1078771307/2000000000 : ℝ)|=(1078771307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632482069/5000000000 : ℝ)|^8287 ≤ (8530437476049/20000000000000 : ℝ)^6239
        have hw : |(2632482069/5000000000 : ℝ)|=(2632482069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534490529/1000000000 : ℝ)*x 0 + (-451088821/2000000000 : ℝ)*x 1 + (658120517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534490529/1000000000 : ℝ)^8287 ≤ (2719657640231/6250000000000 : ℝ)^6239 := by
    have hnat : (534490529 : ℕ)^8287*6250000000000^6239 ≤ 2719657640231^6239*1000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534490529 1000000000 2719657640231 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451088821/2000000000 : ℝ)^8287 ≤ (6916645190169/50000000000000 : ℝ)^6239 := by
    have hnat : (451088821 : ℕ)^8287*50000000000000^6239 ≤ 6916645190169^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451088821 2000000000 6916645190169 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658120517/1250000000 : ℝ)^8287 ≤ (1706087494349/4000000000000 : ℝ)^6239 := by
    have hnat : (658120517 : ℕ)^8287*4000000000000^6239 ≤ 1706087494349^6239*1250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658120517 1250000000 1706087494349 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534490529/1000000000 : ℝ), (-451088821/2000000000 : ℝ), (658120517/1250000000 : ℝ)] ![(2719657640231/6250000000000 : ℝ), (6916645190169/50000000000000 : ℝ), (1706087494349/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534490529/1000000000 : ℝ)|^8287 ≤ (2719657640231/6250000000000 : ℝ)^6239
        have hw : |(534490529/1000000000 : ℝ)|=(534490529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451088821/2000000000 : ℝ)|^8287 ≤ (6916645190169/50000000000000 : ℝ)^6239
        have hw : |(-451088821/2000000000 : ℝ)|=(451088821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658120517/1250000000 : ℝ)|^8287 ≤ (1706087494349/4000000000000 : ℝ)^6239
        have hw : |(658120517/1250000000 : ℝ)|=(658120517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068981057/2000000000 : ℝ)*x 0 + (5264964131/10000000000 : ℝ)*x 1 + (-2255444119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068981057/2000000000 : ℝ)^8287 ≤ (43514522189627/100000000000000 : ℝ)^6239 := by
    have hnat : (1068981057 : ℕ)^8287*100000000000000^6239 ≤ 43514522189627^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068981057 2000000000 43514522189627 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264964131/10000000000 : ℝ)^8287 ≤ (42652187304923/100000000000000 : ℝ)^6239 := by
    have hnat : (5264964131 : ℕ)^8287*100000000000000^6239 ≤ 42652187304923^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264964131 10000000000 42652187304923 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255444119/10000000000 : ℝ)^8287 ≤ (1383329049439/10000000000000 : ℝ)^6239 := by
    have hnat : (2255444119 : ℕ)^8287*10000000000000^6239 ≤ 1383329049439^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255444119 10000000000 1383329049439 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068981057/2000000000 : ℝ), (5264964131/10000000000 : ℝ), (-2255444119/10000000000 : ℝ)] ![(43514522189627/100000000000000 : ℝ), (42652187304923/100000000000000 : ℝ), (1383329049439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068981057/2000000000 : ℝ)|^8287 ≤ (43514522189627/100000000000000 : ℝ)^6239
        have hw : |(1068981057/2000000000 : ℝ)|=(1068981057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264964131/10000000000 : ℝ)|^8287 ≤ (42652187304923/100000000000000 : ℝ)^6239
        have hw : |(5264964131/10000000000 : ℝ)|=(5264964131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2255444119/10000000000 : ℝ)|^8287 ≤ (1383329049439/10000000000000 : ℝ)^6239
        have hw : |(-2255444119/10000000000 : ℝ)|=(2255444119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185740557/5000000000 : ℝ)*x 0 + (13269781/31250000 : ℝ)*x 1 + (4500346001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185740557/5000000000 : ℝ)^8287 ≤ (16658357251129/50000000000000 : ℝ)^6239 := by
    have hnat : (2185740557 : ℕ)^8287*50000000000000^6239 ≤ 16658357251129^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185740557 5000000000 16658357251129 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13269781/31250000 : ℝ)^8287 ≤ (32055781200041/100000000000000 : ℝ)^6239 := by
    have hnat : (13269781 : ℕ)^8287*100000000000000^6239 ≤ 32055781200041^6239*31250000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13269781 31250000 32055781200041 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500346001/10000000000 : ℝ)^8287 ≤ (17313752141747/50000000000000 : ℝ)^6239 := by
    have hnat : (4500346001 : ℕ)^8287*50000000000000^6239 ≤ 17313752141747^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500346001 10000000000 17313752141747 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185740557/5000000000 : ℝ), (13269781/31250000 : ℝ), (4500346001/10000000000 : ℝ)] ![(16658357251129/50000000000000 : ℝ), (32055781200041/100000000000000 : ℝ), (17313752141747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185740557/5000000000 : ℝ)|^8287 ≤ (16658357251129/50000000000000 : ℝ)^6239
        have hw : |(2185740557/5000000000 : ℝ)|=(2185740557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13269781/31250000 : ℝ)|^8287 ≤ (32055781200041/100000000000000 : ℝ)^6239
        have hw : |(13269781/31250000 : ℝ)|=(13269781/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500346001/10000000000 : ℝ)|^8287 ≤ (17313752141747/50000000000000 : ℝ)^6239
        have hw : |(4500346001/10000000000 : ℝ)|=(4500346001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190060423/10000000000 : ℝ)*x 0 + (2632643643/5000000000 : ℝ)*x 1 + (1078706487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190060423/10000000000 : ℝ)^8287 ≤ (831449214929/6250000000000 : ℝ)^6239 := by
    have hnat : (2190060423 : ℕ)^8287*6250000000000^6239 ≤ 831449214929^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190060423 10000000000 831449214929 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632643643/5000000000 : ℝ)^8287 ≤ (1066391615391/2500000000000 : ℝ)^6239 := by
    have hnat : (2632643643 : ℕ)^8287*2500000000000^6239 ≤ 1066391615391^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632643643 5000000000 1066391615391 2500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078706487/2000000000 : ℝ)^8287 ≤ (44041147920289/100000000000000 : ℝ)^6239 := by
    have hnat : (1078706487 : ℕ)^8287*100000000000000^6239 ≤ 44041147920289^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078706487 2000000000 44041147920289 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190060423/10000000000 : ℝ), (2632643643/5000000000 : ℝ), (1078706487/2000000000 : ℝ)] ![(831449214929/6250000000000 : ℝ), (1066391615391/2500000000000 : ℝ), (44041147920289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190060423/10000000000 : ℝ)|^8287 ≤ (831449214929/6250000000000 : ℝ)^6239
        have hw : |(-2190060423/10000000000 : ℝ)|=(2190060423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632643643/5000000000 : ℝ)|^8287 ≤ (1066391615391/2500000000000 : ℝ)^6239
        have hw : |(2632643643/5000000000 : ℝ)|=(2632643643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078706487/2000000000 : ℝ)|^8287 ≤ (44041147920289/100000000000000 : ℝ)^6239
        have hw : |(1078706487/2000000000 : ℝ)|=(1078706487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312368119/10000000000 : ℝ)*x 0 + (-2126876537/10000000000 : ℝ)*x 1 + (2696766039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312368119/10000000000 : ℝ)^8287 ≤ (43163025246927/100000000000000 : ℝ)^6239 := by
    have hnat : (5312368119 : ℕ)^8287*100000000000000^6239 ≤ 43163025246927^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312368119 10000000000 43163025246927 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126876537/10000000000 : ℝ)^8287 ≤ (3198957670979/25000000000000 : ℝ)^6239 := by
    have hnat : (2126876537 : ℕ)^8287*25000000000000^6239 ≤ 3198957670979^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126876537 10000000000 3198957670979 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696766039/5000000000 : ℝ)^8287 ≤ (11010286012071/25000000000000 : ℝ)^6239 := by
    have hnat : (2696766039 : ℕ)^8287*25000000000000^6239 ≤ 11010286012071^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696766039 5000000000 11010286012071 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312368119/10000000000 : ℝ), (-2126876537/10000000000 : ℝ), (2696766039/5000000000 : ℝ)] ![(43163025246927/100000000000000 : ℝ), (3198957670979/25000000000000 : ℝ), (11010286012071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312368119/10000000000 : ℝ)|^8287 ≤ (43163025246927/100000000000000 : ℝ)^6239
        have hw : |(5312368119/10000000000 : ℝ)|=(5312368119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126876537/10000000000 : ℝ)|^8287 ≤ (3198957670979/25000000000000 : ℝ)^6239
        have hw : |(-2126876537/10000000000 : ℝ)|=(2126876537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696766039/5000000000 : ℝ)|^8287 ≤ (11010286012071/25000000000000 : ℝ)^6239
        have hw : |(2696766039/5000000000 : ℝ)|=(2696766039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656184441/5000000000 : ℝ)*x 0 + (1348383001/2500000000 : ℝ)*x 1 + (-2126875607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656184441/5000000000 : ℝ)^8287 ≤ (21581516740651/50000000000000 : ℝ)^6239 := by
    have hnat : (2656184441 : ℕ)^8287*50000000000000^6239 ≤ 21581516740651^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656184441 5000000000 21581516740651 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348383001/2500000000 : ℝ)^8287 ≤ (11010285811421/25000000000000 : ℝ)^6239 := by
    have hnat : (1348383001 : ℕ)^8287*25000000000000^6239 ≤ 11010285811421^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348383001 2500000000 11010285811421 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126875607/10000000000 : ℝ)^8287 ≤ (12795823252159/100000000000000 : ℝ)^6239 := by
    have hnat : (2126875607 : ℕ)^8287*100000000000000^6239 ≤ 12795823252159^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126875607 10000000000 12795823252159 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656184441/5000000000 : ℝ), (1348383001/2500000000 : ℝ), (-2126875607/10000000000 : ℝ)] ![(21581516740651/50000000000000 : ℝ), (11010285811421/25000000000000 : ℝ), (12795823252159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656184441/5000000000 : ℝ)|^8287 ≤ (21581516740651/50000000000000 : ℝ)^6239
        have hw : |(2656184441/5000000000 : ℝ)|=(2656184441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348383001/2500000000 : ℝ)|^8287 ≤ (11010285811421/25000000000000 : ℝ)^6239
        have hw : |(1348383001/2500000000 : ℝ)|=(1348383001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126875607/10000000000 : ℝ)|^8287 ≤ (12795823252159/100000000000000 : ℝ)^6239
        have hw : |(-2126875607/10000000000 : ℝ)|=(2126875607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s8_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371491359/10000000000 : ℝ)*x 0 + (2249854617/5000000000 : ℝ)*x 1 + (2123484287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371491359/10000000000 : ℝ)^8287 ≤ (33316818214027/100000000000000 : ℝ)^6239 := by
    have hnat : (4371491359 : ℕ)^8287*100000000000000^6239 ≤ 33316818214027^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371491359 10000000000 33316818214027 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249854617/5000000000 : ℝ)^8287 ≤ (34620996574833/100000000000000 : ℝ)^6239 := by
    have hnat : (2249854617 : ℕ)^8287*100000000000000^6239 ≤ 34620996574833^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249854617 5000000000 34620996574833 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123484287/5000000000 : ℝ)^8287 ≤ (32062185200307/100000000000000 : ℝ)^6239 := by
    have hnat : (2123484287 : ℕ)^8287*100000000000000^6239 ≤ 32062185200307^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123484287 5000000000 32062185200307 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371491359/10000000000 : ℝ), (2249854617/5000000000 : ℝ), (2123484287/5000000000 : ℝ)] ![(33316818214027/100000000000000 : ℝ), (34620996574833/100000000000000 : ℝ), (32062185200307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371491359/10000000000 : ℝ)|^8287 ≤ (33316818214027/100000000000000 : ℝ)^6239
        have hw : |(4371491359/10000000000 : ℝ)|=(4371491359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249854617/5000000000 : ℝ)|^8287 ≤ (34620996574833/100000000000000 : ℝ)^6239
        have hw : |(2249854617/5000000000 : ℝ)|=(2249854617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123484287/5000000000 : ℝ)|^8287 ≤ (32062185200307/100000000000000 : ℝ)^6239
        have hw : |(2123484287/5000000000 : ℝ)|=(2123484287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1129/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (4143/1024 : ℝ) ≤ (2937748405828181/20000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^4143 ≤ (2937748405828181/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4143*20000000000000000000^1024 ≤ 2937748405828181^1024*12500^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 2937748405828181 20000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (2937748405828181/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7011/50000 : ℝ) ^ (4143/1024 : ℝ) ≤ (8831201013501661/25000000000000000000 : ℝ) := by
    have hpowers : (7011/50000 : ℝ)^4143 ≤ (8831201013501661/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7011 : ℕ)^4143*25000000000000000000^1024 ≤ 8831201013501661^1024*50000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7011 50000 8831201013501661 25000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7011/50000 : ℝ)) (X := (8831201013501661/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002937748405828181/10000000000000000000 : ℝ) ≤ (250018150626149/250000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (10002937748405828181/10000000000000000000 : ℝ)^1024 ≤ (250018150626149/250000000000000 : ℝ)^4143 := by
      have hnat : (10002937748405828181 : ℕ)^1024*250000000000000^4143 ≤ 250018150626149^4143*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002937748405828181 10000000000000000000 250018150626149 250000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250018150626149/250000000000000 : ℝ)) (X := (10002937748405828181/10000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050013546083147549/100000000000000000000 : ℝ) ≤ (5000617960807161/5000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (100050013546083147549/100000000000000000000 : ℝ)^1024 ≤ (5000617960807161/5000000000000000 : ℝ)^4143 := by
      have hnat : (100050013546083147549 : ℕ)^1024*5000000000000000^4143 ≤ 5000617960807161^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050013546083147549 100000000000000000000 5000617960807161 5000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000617960807161/5000000000000000 : ℝ)) (X := (100050013546083147549/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508831201013501661/12500000000000000000 : ℝ) ≤ (2500436454545671/2500000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (12508831201013501661/12500000000000000000 : ℝ)^1024 ≤ (2500436454545671/2500000000000000 : ℝ)^4143 := by
      have hnat : (12508831201013501661 : ℕ)^1024*2500000000000000^4143 ≤ 2500436454545671^4143*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508831201013501661 12500000000000000000 2500436454545671 2500000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500436454545671/2500000000000000 : ℝ)) (X := (12508831201013501661/12500000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2937748405828181/20000000000000000000 : ℝ) ≤ ((1708154595471769633/1708750000000000000 : ℝ)+2*(254948284181/136700000000000 : ℝ)*(1411/12500 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1708154595471769633/1708750000000000000 : ℝ)+2*(254948284181/136700000000000 : ℝ)*(1411/12500 : ℝ)=(250018150626149/250000000000000 : ℝ) by norm_num, show 1+2*(2937748405828181/20000000000000000000 : ℝ)=(10002937748405828181/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8831201013501661/25000000000000000000 : ℝ)+(2937748405828181/20000000000000000000 : ℝ) ≤ ((1708154595471769633/1708750000000000000 : ℝ)+(254948284181/136700000000000 : ℝ)*((7011/50000 : ℝ)+(1411/12500 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (1708154595471769633/1708750000000000000 : ℝ)+(254948284181/136700000000000 : ℝ)*((7011/50000 : ℝ)+(1411/12500 : ℝ))=(5000617960807161/5000000000000000 : ℝ) by norm_num, show 1+(8831201013501661/25000000000000000000 : ℝ)+(2937748405828181/20000000000000000000 : ℝ)=(100050013546083147549/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8831201013501661/25000000000000000000 : ℝ) ≤ ((1708154595471769633/1708750000000000000 : ℝ)+2*(254948284181/136700000000000 : ℝ)*(7011/50000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1708154595471769633/1708750000000000000 : ℝ)+2*(254948284181/136700000000000 : ℝ)*(7011/50000 : ℝ)=(2500436454545671/2500000000000000 : ℝ) by norm_num, show 1+2*(8831201013501661/25000000000000000000 : ℝ)=(12508831201013501661/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1708154595471769633/1708750000000000000 : ℝ)*(X 1 0+X 2 0)+(254948284181/136700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (1708154595471769633/1708750000000000000 : ℝ)) (alpha := (254948284181/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1708154595471769633/1708750000000000000 : ℝ)*(X 0 1+X 2 1)+(254948284181/136700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (1708154595471769633/1708750000000000000 : ℝ)) (alpha := (254948284181/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1708154595471769633/1708750000000000000 : ℝ)*(X 0 2+X 1 2)+(254948284181/136700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (1708154595471769633/1708750000000000000 : ℝ)) (alpha := (254948284181/136700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190055719/10000000000 : ℝ)*X 0 0+(1078771307/2000000000 : ℝ)*X 0 1+(2632482069/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534490529/1000000000 : ℝ)*X 1 0+(-451088821/2000000000 : ℝ)*X 1 1+(658120517/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068981057/2000000000 : ℝ)*X 2 0+(5264964131/10000000000 : ℝ)*X 2 1+(-2255444119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185740557/5000000000 : ℝ)*X 0 0+(13269781/31250000 : ℝ)*X 0 1+(4500346001/10000000000 : ℝ)*X 0 2+(2185740557/5000000000 : ℝ)*X 1 0+(13269781/31250000 : ℝ)*X 1 1+(4500346001/10000000000 : ℝ)*X 1 2+(2185740557/5000000000 : ℝ)*X 2 0+(13269781/31250000 : ℝ)*X 2 1+(4500346001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2190060423/10000000000 : ℝ)*X 0 0+(2632643643/5000000000 : ℝ)*X 0 1+(1078706487/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312368119/10000000000 : ℝ)*X 1 0+(-2126876537/10000000000 : ℝ)*X 1 1+(2696766039/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656184441/5000000000 : ℝ)*X 2 0+(1348383001/2500000000 : ℝ)*X 2 1+(-2126875607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371491359/10000000000 : ℝ)*X 0 0+(2249854617/5000000000 : ℝ)*X 0 1+(2123484287/5000000000 : ℝ)*X 0 2+(4371491359/10000000000 : ℝ)*X 1 0+(2249854617/5000000000 : ℝ)*X 1 1+(2123484287/5000000000 : ℝ)*X 1 2+(4371491359/10000000000 : ℝ)*X 2 0+(2249854617/5000000000 : ℝ)*X 2 1+(2123484287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38820541883097008023323/6835000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1149143871/100000000000000 : ℝ)*(base19) + (1070401611/100000000000000 : ℝ)*(base23) + (19103879/50000000000000 : ℝ)*(lower2) + (30702873/20000000000000 : ℝ)*(upper3) + (77363691/100000000000000 : ℝ)*(upper5) + (5847631807950303/100000000000000 : ℝ)*(major0) + (5847631807950303/100000000000000 : ℝ)*(major1) + (5847631807950303/100000000000000 : ℝ)*(major2) + (1939610585923609/25000000000000 : ℝ)*(sp0) + (3879235727664913/50000000000000 : ℝ)*(sp1) + (3879235767036043/50000000000000 : ℝ)*(sp2) + (1968386874770047/50000000000000 : ℝ)*(sp3) + (1513038963/5000000000000 : ℝ)*(sp4) + (4268141121/25000000000000 : ℝ)*(sp7) + (3936790822104579/100000000000000 : ℝ)*(f.failure) + (7758472604473697/100000000000000 : ℝ)*(f.sum) + (25610514382163/6835000000000000000000000000 : ℝ)*base65 + (648855378932586299/170875000000000000000000000000000 : ℝ)*base67 + (11941967276663701/170875000000000000000000000000000 : ℝ)*base70 + (1066485723661413701/170875000000000000000000000000000 : ℝ)*base72 + (80583667545833/6835000000000000000000000000 : ℝ)*base73 + (537303925853836299/170875000000000000000000000000000 : ℝ)*base75 + (1607674710839836299/170875000000000000000000000000000 : ℝ)*base77 + (3685580315577663701/170875000000000000000000000000000 : ℝ)*base80 + (32443766891383/6835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (73371423/10000000000000000000000 : ℝ)*base89 + (73371423/10000000000000000000000 : ℝ)*base91 + (73371423/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106024184220880843974381327/21359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431478987/50000000000000 : ℝ)*(base19) + (296723671/20000000000000 : ℝ)*(base23) + (209276543/50000000000000 : ℝ)*(lower2) + (59572461/50000000000000 : ℝ)*(upper3) + (1702263/6250000000000 : ℝ)*(upper5) + (1469278387874127/25000000000000 : ℝ)*(major0) + (1469278387874127/25000000000000 : ℝ)*(major1) + (1469278387874127/25000000000000 : ℝ)*(major2) + (23560512127/50000000000000 : ℝ)*(sp2) + (29604967/25000000000000 : ℝ)*(sp3) + (7797588173350533/100000000000000 : ℝ)*(sp4) + (7797587310392559/100000000000000 : ℝ)*(sp5) + (1949384892176981/25000000000000 : ℝ)*(sp6) + (19783193228809/500000000000 : ℝ)*(sp7) + (989159691045417/25000000000000 : ℝ)*(f.failure) + (7797588173350533/100000000000000 : ℝ)*(f.sum) + (23640391101707/6835000000000000000000000000 : ℝ)*base66 + (64618895367760391/42718750000000000000000000000000 : ℝ)*base67 + (87049497490416641/42718750000000000000000000000000 : ℝ)*base69 + (36717123513854141/42718750000000000000000000000000 : ℝ)*base71 + (47640946008847/6835000000000000000000000000 : ℝ)*base74 + (1082545866389239609/42718750000000000000000000000000 : ℝ)*base76 + (104393156758260391/42718750000000000000000000000000 : ℝ)*base77 + (58719086827364609/42718750000000000000000000000000 : ℝ)*base80 + (17804734548671/3417500000000000000000000000 : ℝ)*base82 + (19026429/2500000000000000000000 : ℝ)*base89 + (19026429/2500000000000000000000 : ℝ)*base91 + (19026429/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1094_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1094_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1094_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1094_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
