-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1243_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:09.540316+00:00
-- url     : https://prove2.me/submissions/724c0703-5b3b-4b13-b8d4-3f31268850f4

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
theorem support_rectangle_w1243_s6_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119484181/10000000000 : ℝ)*x 0 + (1078274801/2000000000 : ℝ)*x 1 + (5267044571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119484181/10000000000 : ℝ)^2109 ≤ (6444493945089/50000000000000 : ℝ)^1597 := by
    have hnat : (2119484181 : ℕ)^2109*50000000000000^1597 ≤ 6444493945089^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119484181 10000000000 6444493945089 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078274801/2000000000 : ℝ)^2109 ≤ (11056610574707/25000000000000 : ℝ)^1597 := by
    have hnat : (1078274801 : ℕ)^2109*25000000000000^1597 ≤ 11056610574707^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078274801 2000000000 11056610574707 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267044571/10000000000 : ℝ)^2109 ≤ (42884569798549/100000000000000 : ℝ)^1597 := by
    have hnat : (5267044571 : ℕ)^2109*100000000000000^1597 ≤ 42884569798549^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267044571 10000000000 42884569798549 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119484181/10000000000 : ℝ), (1078274801/2000000000 : ℝ), (5267044571/10000000000 : ℝ)] ![(6444493945089/50000000000000 : ℝ), (11056610574707/25000000000000 : ℝ), (42884569798549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119484181/10000000000 : ℝ)|^2109 ≤ (6444493945089/50000000000000 : ℝ)^1597
        have hw : |(-2119484181/10000000000 : ℝ)|=(2119484181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078274801/2000000000 : ℝ)|^2109 ≤ (11056610574707/25000000000000 : ℝ)^1597
        have hw : |(1078274801/2000000000 : ℝ)|=(1078274801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267044571/10000000000 : ℝ)|^2109 ≤ (42884569798549/100000000000000 : ℝ)^1597
        have hw : |(5267044571/10000000000 : ℝ)|=(5267044571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344353489/10000000000 : ℝ)*x 0 + (-2182524633/10000000000 : ℝ)*x 1 + (5267044697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344353489/10000000000 : ℝ)^2109 ≤ (21858888094789/50000000000000 : ℝ)^1597 := by
    have hnat : (5344353489 : ℕ)^2109*50000000000000^1597 ≤ 21858888094789^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344353489 10000000000 21858888094789 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182524633/10000000000 : ℝ)^2109 ≤ (1339765264313/10000000000000 : ℝ)^1597 := by
    have hnat : (2182524633 : ℕ)^2109*10000000000000^1597 ≤ 1339765264313^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182524633 10000000000 1339765264313 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267044697/10000000000 : ℝ)^2109 ≤ (5360571394169/12500000000000 : ℝ)^1597 := by
    have hnat : (5267044697 : ℕ)^2109*12500000000000^1597 ≤ 5360571394169^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267044697 10000000000 5360571394169 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344353489/10000000000 : ℝ), (-2182524633/10000000000 : ℝ), (5267044697/10000000000 : ℝ)] ![(21858888094789/50000000000000 : ℝ), (1339765264313/10000000000000 : ℝ), (5360571394169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344353489/10000000000 : ℝ)|^2109 ≤ (21858888094789/50000000000000 : ℝ)^1597
        have hw : |(5344353489/10000000000 : ℝ)|=(5344353489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182524633/10000000000 : ℝ)|^2109 ≤ (1339765264313/10000000000000 : ℝ)^1597
        have hw : |(-2182524633/10000000000 : ℝ)|=(2182524633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267044697/10000000000 : ℝ)|^2109 ≤ (5360571394169/12500000000000 : ℝ)^1597
        have hw : |(5267044697/10000000000 : ℝ)|=(5267044697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344353279/10000000000 : ℝ)*x 0 + (1053408941/2000000000 : ℝ)*x 1 + (-2182524903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344353279/10000000000 : ℝ)^2109 ≤ (43717773921/100000000000 : ℝ)^1597 := by
    have hnat : (5344353279 : ℕ)^2109*100000000000^1597 ≤ 43717773921^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344353279 10000000000 43717773921 100000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053408941/2000000000 : ℝ)^2109 ≤ (10721142809843/25000000000000 : ℝ)^1597 := by
    have hnat : (1053408941 : ℕ)^2109*25000000000000^1597 ≤ 10721142809843^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053408941 2000000000 10721142809843 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182524903/10000000000 : ℝ)^2109 ≤ (3349413707981/25000000000000 : ℝ)^1597 := by
    have hnat : (2182524903 : ℕ)^2109*25000000000000^1597 ≤ 3349413707981^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182524903 10000000000 3349413707981 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344353279/10000000000 : ℝ), (1053408941/2000000000 : ℝ), (-2182524903/10000000000 : ℝ)] ![(43717773921/100000000000 : ℝ), (10721142809843/25000000000000 : ℝ), (3349413707981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344353279/10000000000 : ℝ)|^2109 ≤ (43717773921/100000000000 : ℝ)^1597
        have hw : |(5344353279/10000000000 : ℝ)|=(5344353279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053408941/2000000000 : ℝ)|^2109 ≤ (10721142809843/25000000000000 : ℝ)^1597
        have hw : |(1053408941/2000000000 : ℝ)|=(1053408941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182524903/10000000000 : ℝ)|^2109 ≤ (3349413707981/25000000000000 : ℝ)^1597
        have hw : |(-2182524903/10000000000 : ℝ)|=(2182524903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2175313033/5000000000 : ℝ)*x 0 + (845254821/2000000000 : ℝ)*x 1 + (55981669/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175313033/5000000000 : ℝ)^2109 ≤ (33317395450417/100000000000000 : ℝ)^1597 := by
    have hnat : (2175313033 : ℕ)^2109*100000000000000^1597 ≤ 33317395450417^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175313033 5000000000 33317395450417 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845254821/2000000000 : ℝ)^2109 ≤ (32065592218361/100000000000000 : ℝ)^1597 := by
    have hnat : (845254821 : ℕ)^2109*100000000000000^1597 ≤ 32065592218361^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845254821 2000000000 32065592218361 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55981669/125000000 : ℝ)^2109 ≤ (8654253080781/25000000000000 : ℝ)^1597 := by
    have hnat : (55981669 : ℕ)^2109*25000000000000^1597 ≤ 8654253080781^1597*125000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55981669 125000000 8654253080781 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175313033/5000000000 : ℝ), (845254821/2000000000 : ℝ), (55981669/125000000 : ℝ)] ![(33317395450417/100000000000000 : ℝ), (32065592218361/100000000000000 : ℝ), (8654253080781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175313033/5000000000 : ℝ)|^2109 ≤ (33317395450417/100000000000000 : ℝ)^1597
        have hw : |(2175313033/5000000000 : ℝ)|=(2175313033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845254821/2000000000 : ℝ)|^2109 ≤ (32065592218361/100000000000000 : ℝ)^1597
        have hw : |(845254821/2000000000 : ℝ)|=(845254821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55981669/125000000 : ℝ)|^2109 ≤ (8654253080781/25000000000000 : ℝ)^1597
        have hw : |(55981669/125000000 : ℝ)|=(55981669/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119488847/10000000000 : ℝ)*x 0 + (1053471823/2000000000 : ℝ)*x 1 + (269552917/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119488847/10000000000 : ℝ)^2109 ≤ (12889025362033/100000000000000 : ℝ)^1597 := by
    have hnat : (2119488847 : ℕ)^2109*100000000000000^1597 ≤ 12889025362033^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119488847 10000000000 12889025362033 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053471823/2000000000 : ℝ)^2109 ≤ (42887951936289/100000000000000 : ℝ)^1597 := by
    have hnat : (1053471823 : ℕ)^2109*100000000000000^1597 ≤ 42887951936289^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053471823 2000000000 42887951936289 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269552917/500000000 : ℝ)^2109 ≤ (11055755672237/25000000000000 : ℝ)^1597 := by
    have hnat : (269552917 : ℕ)^2109*25000000000000^1597 ≤ 11055755672237^1597*500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269552917 500000000 11055755672237 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119488847/10000000000 : ℝ), (1053471823/2000000000 : ℝ), (269552917/500000000 : ℝ)] ![(12889025362033/100000000000000 : ℝ), (42887951936289/100000000000000 : ℝ), (11055755672237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119488847/10000000000 : ℝ)|^2109 ≤ (12889025362033/100000000000000 : ℝ)^1597
        have hw : |(-2119488847/10000000000 : ℝ)|=(2119488847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053471823/2000000000 : ℝ)|^2109 ≤ (42887951936289/100000000000000 : ℝ)^1597
        have hw : |(1053471823/2000000000 : ℝ)|=(1053471823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269552917/500000000 : ℝ)|^2109 ≤ (11055755672237/25000000000000 : ℝ)^1597
        have hw : |(269552917/500000000 : ℝ)|=(269552917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656313941/5000000000 : ℝ)*x 0 + (-1029255719/5000000000 : ℝ)*x 1 + (539105827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656313941/5000000000 : ℝ)^2109 ≤ (43375378783523/100000000000000 : ℝ)^1597 := by
    have hnat : (2656313941 : ℕ)^2109*100000000000000^1597 ≤ 43375378783523^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656313941 5000000000 43375378783523 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029255719/5000000000 : ℝ)^2109 ≤ (1240159926401/10000000000000 : ℝ)^1597 := by
    have hnat : (1029255719 : ℕ)^2109*10000000000000^1597 ≤ 1240159926401^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029255719 5000000000 1240159926401 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539105827/1000000000 : ℝ)^2109 ≤ (44223021930643/100000000000000 : ℝ)^1597 := by
    have hnat : (539105827 : ℕ)^2109*100000000000000^1597 ≤ 44223021930643^1597*1000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539105827 1000000000 44223021930643 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656313941/5000000000 : ℝ), (-1029255719/5000000000 : ℝ), (539105827/1000000000 : ℝ)] ![(43375378783523/100000000000000 : ℝ), (1240159926401/10000000000000 : ℝ), (44223021930643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656313941/5000000000 : ℝ)|^2109 ≤ (43375378783523/100000000000000 : ℝ)^1597
        have hw : |(2656313941/5000000000 : ℝ)|=(2656313941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029255719/5000000000 : ℝ)|^2109 ≤ (1240159926401/10000000000000 : ℝ)^1597
        have hw : |(-1029255719/5000000000 : ℝ)|=(1029255719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539105827/1000000000 : ℝ)|^2109 ≤ (44223021930643/100000000000000 : ℝ)^1597
        have hw : |(539105827/1000000000 : ℝ)|=(539105827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656313801/5000000000 : ℝ)*x 0 + (5391058569/10000000000 : ℝ)*x 1 + (-2058511411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656313801/5000000000 : ℝ)^2109 ≤ (1084384394113/2500000000000 : ℝ)^1597 := by
    have hnat : (2656313801 : ℕ)^2109*2500000000000^1597 ≤ 1084384394113^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656313801 5000000000 1084384394113 2500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391058569/10000000000 : ℝ)^2109 ≤ (44223025169689/100000000000000 : ℝ)^1597 := by
    have hnat : (5391058569 : ℕ)^2109*100000000000000^1597 ≤ 44223025169689^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391058569 10000000000 44223025169689 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058511411/10000000000 : ℝ)^2109 ≤ (6200799524599/50000000000000 : ℝ)^1597 := by
    have hnat : (2058511411 : ℕ)^2109*50000000000000^1597 ≤ 6200799524599^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058511411 10000000000 6200799524599 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656313801/5000000000 : ℝ), (5391058569/10000000000 : ℝ), (-2058511411/10000000000 : ℝ)] ![(1084384394113/2500000000000 : ℝ), (44223025169689/100000000000000 : ℝ), (6200799524599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656313801/5000000000 : ℝ)|^2109 ≤ (1084384394113/2500000000000 : ℝ)^1597
        have hw : |(2656313801/5000000000 : ℝ)|=(2656313801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391058569/10000000000 : ℝ)|^2109 ≤ (44223025169689/100000000000000 : ℝ)^1597
        have hw : |(5391058569/10000000000 : ℝ)|=(5391058569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058511411/10000000000 : ℝ)|^2109 ≤ (6200799524599/50000000000000 : ℝ)^1597
        have hw : |(-2058511411/10000000000 : ℝ)|=(2058511411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s6_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350636043/10000000000 : ℝ)*x 0 + (1119473827/2500000000 : ℝ)*x 1 + (422691419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350636043/10000000000 : ℝ)^2109 ≤ (33317496350397/100000000000000 : ℝ)^1597 := by
    have hnat : (4350636043 : ℕ)^2109*100000000000000^1597 ≤ 33317496350397^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350636043 10000000000 33317496350397 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119473827/2500000000 : ℝ)^2109 ≤ (1384419913301/4000000000000 : ℝ)^1597 := by
    have hnat : (1119473827 : ℕ)^2109*4000000000000^1597 ≤ 1384419913301^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119473827 2500000000 1384419913301 4000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422691419/1000000000 : ℝ)^2109 ≤ (32072005812317/100000000000000 : ℝ)^1597 := by
    have hnat : (422691419 : ℕ)^2109*100000000000000^1597 ≤ 32072005812317^1597*1000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422691419 1000000000 32072005812317 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350636043/10000000000 : ℝ), (1119473827/2500000000 : ℝ), (422691419/1000000000 : ℝ)] ![(33317496350397/100000000000000 : ℝ), (1384419913301/4000000000000 : ℝ), (32072005812317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350636043/10000000000 : ℝ)|^2109 ≤ (33317496350397/100000000000000 : ℝ)^1597
        have hw : |(4350636043/10000000000 : ℝ)|=(4350636043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119473827/2500000000 : ℝ)|^2109 ≤ (1384419913301/4000000000000 : ℝ)^1597
        have hw : |(1119473827/2500000000 : ℝ)|=(1119473827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422691419/1000000000 : ℝ)|^2109 ≤ (32072005812317/100000000000000 : ℝ)^1597
        have hw : |(422691419/1000000000 : ℝ)|=(422691419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (459/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2291/20000 : ℝ) ^ (8435/2048 : ℝ) ≤ (13314594256623357/100000000000000000000 : ℝ) := by
    have hpowers : (2291/20000 : ℝ)^8435 ≤ (13314594256623357/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2291 : ℕ)^8435*100000000000000000000^2048 ≤ 13314594256623357^2048*20000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 20000 13314594256623357 100000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/20000 : ℝ)) (X := (13314594256623357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14131/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (1580620507359701/5000000000000000000 : ℝ) := by
    have hpowers : (14131/100000 : ℝ)^8435 ≤ (1580620507359701/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14131 : ℕ)^8435*5000000000000000000^2048 ≤ 1580620507359701^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14131 100000 1580620507359701 5000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14131/100000 : ℝ)) (X := (1580620507359701/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013314594256623357/50000000000000000000 : ℝ) ≤ (10000646485840457/10000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50013314594256623357/50000000000000000000 : ℝ)^2048 ≤ (10000646485840457/10000000000000000 : ℝ)^8435 := by
      have hnat : (50013314594256623357 : ℕ)^2048*10000000000000000^8435 ≤ 10000646485840457^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013314594256623357 50000000000000000000 10000646485840457 10000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646485840457/10000000000000000 : ℝ)) (X := (50013314594256623357/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044927004403817377/100000000000000000000 : ℝ) ≤ (1250136329073341/1250000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (100044927004403817377/100000000000000000000 : ℝ)^2048 ≤ (1250136329073341/1250000000000000 : ℝ)^8435 := by
      have hnat : (100044927004403817377 : ℕ)^2048*1250000000000000^8435 ≤ 1250136329073341^8435*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044927004403817377 100000000000000000000 1250136329073341 1250000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250136329073341/1250000000000000 : ℝ)) (X := (100044927004403817377/100000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501580620507359701/2500000000000000000 : ℝ) ≤ (10001534779332999/10000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (2501580620507359701/2500000000000000000 : ℝ)^2048 ≤ (10001534779332999/10000000000000000 : ℝ)^8435 := by
      have hnat : (2501580620507359701 : ℕ)^2048*10000000000000000^8435 ≤ 10001534779332999^8435*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501580620507359701 2500000000000000000 10001534779332999 10000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001534779332999/10000000000000000 : ℝ)) (X := (2501580620507359701/2500000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13314594256623357/100000000000000000000 : ℝ) ≤ ((13375777297075997161/13380000000000000000 : ℝ)+2*(444146746271/267600000000000 : ℝ)*(2291/20000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (13375777297075997161/13380000000000000000 : ℝ)+2*(444146746271/267600000000000 : ℝ)*(2291/20000 : ℝ)=(10000646485840457/10000000000000000 : ℝ) by norm_num, show 1+2*(13314594256623357/100000000000000000000 : ℝ)=(50013314594256623357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1580620507359701/5000000000000000000 : ℝ)+(13314594256623357/100000000000000000000 : ℝ) ≤ ((13375777297075997161/13380000000000000000 : ℝ)+(444146746271/267600000000000 : ℝ)*((14131/100000 : ℝ)+(2291/20000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (13375777297075997161/13380000000000000000 : ℝ)+(444146746271/267600000000000 : ℝ)*((14131/100000 : ℝ)+(2291/20000 : ℝ))=(1250136329073341/1250000000000000 : ℝ) by norm_num, show 1+(1580620507359701/5000000000000000000 : ℝ)+(13314594256623357/100000000000000000000 : ℝ)=(100044927004403817377/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1580620507359701/5000000000000000000 : ℝ) ≤ ((13375777297075997161/13380000000000000000 : ℝ)+2*(444146746271/267600000000000 : ℝ)*(14131/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (13375777297075997161/13380000000000000000 : ℝ)+2*(444146746271/267600000000000 : ℝ)*(14131/100000 : ℝ)=(10001534779332999/10000000000000000 : ℝ) by norm_num, show 1+2*(1580620507359701/5000000000000000000 : ℝ)=(2501580620507359701/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13375777297075997161/13380000000000000000 : ℝ)*(X 1 0+X 2 0)+(444146746271/267600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13375777297075997161/13380000000000000000 : ℝ)) (alpha := (444146746271/267600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13375777297075997161/13380000000000000000 : ℝ)*(X 0 1+X 2 1)+(444146746271/267600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13375777297075997161/13380000000000000000 : ℝ)) (alpha := (444146746271/267600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13375777297075997161/13380000000000000000 : ℝ)*(X 0 2+X 1 2)+(444146746271/267600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13375777297075997161/13380000000000000000 : ℝ)) (alpha := (444146746271/267600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119484181/10000000000 : ℝ)*X 0 0+(1078274801/2000000000 : ℝ)*X 0 1+(5267044571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344353489/10000000000 : ℝ)*X 1 0+(-2182524633/10000000000 : ℝ)*X 1 1+(5267044697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344353279/10000000000 : ℝ)*X 2 0+(1053408941/2000000000 : ℝ)*X 2 1+(-2182524903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175313033/5000000000 : ℝ)*X 0 0+(845254821/2000000000 : ℝ)*X 0 1+(55981669/125000000 : ℝ)*X 0 2+(2175313033/5000000000 : ℝ)*X 1 0+(845254821/2000000000 : ℝ)*X 1 1+(55981669/125000000 : ℝ)*X 1 2+(2175313033/5000000000 : ℝ)*X 2 0+(845254821/2000000000 : ℝ)*X 2 1+(55981669/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119488847/10000000000 : ℝ)*X 0 0+(1053471823/2000000000 : ℝ)*X 0 1+(269552917/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656313941/5000000000 : ℝ)*X 1 0+(-1029255719/5000000000 : ℝ)*X 1 1+(539105827/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656313801/5000000000 : ℝ)*X 2 0+(5391058569/10000000000 : ℝ)*X 2 1+(-2058511411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350636043/10000000000 : ℝ)*X 0 0+(1119473827/2500000000 : ℝ)*X 0 1+(422691419/1000000000 : ℝ)*X 0 2+(4350636043/10000000000 : ℝ)*X 1 0+(1119473827/2500000000 : ℝ)*X 1 1+(422691419/1000000000 : ℝ)*X 1 2+(4350636043/10000000000 : ℝ)*X 2 0+(1119473827/2500000000 : ℝ)*X 2 1+(422691419/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2811342060730999738798219497/223000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60570339/3125000000000 : ℝ)*(base19) + (1587883901/100000000000000 : ℝ)*(base23) + (3011661/50000000000000 : ℝ)*(upper2) + (306763097/100000000000000 : ℝ)*(upper3) + (6003758335165941/100000000000000 : ℝ)*(major0) + (6003758335165941/100000000000000 : ℝ)*(major1) + (6003758335165941/100000000000000 : ℝ)*(major2) + (2010806080437807/25000000000000 : ℝ)*(sp0) + (8043279792264077/100000000000000 : ℝ)*(sp1) + (8043272463387359/100000000000000 : ℝ)*(sp2) + (991050401016357/25000000000000 : ℝ)*(sp3) + (57408763697/100000000000000 : ℝ)*(sp4) + (1535848733/20000000000000 : ℝ)*(sp6) + (32915521017/100000000000000 : ℝ)*(sp7) + (792846903917289/20000000000000 : ℝ)*(f.failure) + (4021640865257463/50000000000000 : ℝ)*(f.sum) + (10125954584583/4460000000000000000000000000 : ℝ)*base66 + (6849093971527481167/446000000000000000000000000000000 : ℝ)*base67 + (498171052325481167/446000000000000000000000000000000 : ℝ)*base69 + (3882404479721481167/446000000000000000000000000000000 : ℝ)*base71 + (2847422385237/4460000000000000000000000000 : ℝ)*base73 + (1418990010879481167/446000000000000000000000000000000 : ℝ)*base75 + (3187925909973481167/446000000000000000000000000000000 : ℝ)*base77 + (5853611631017481167/446000000000000000000000000000000 : ℝ)*base79 + (14896660243743/4460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (200523/125000000000000000000 : ℝ)*base89 + (200523/125000000000000000000 : ℝ)*base91 + (200523/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (356326687457615566745600927/111500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4051343/4000000000000 : ℝ)*(base8) + (375541379/100000000000000 : ℝ)*(base21) + (16531399/50000000000000 : ℝ)*(upper3) + (10065139/20000000000000 : ℝ)*(lower4) + (46878943/25000000000000 : ℝ)*(upper5) + (6034256072597807/100000000000000 : ℝ)*(major0) + (6034256072597807/100000000000000 : ℝ)*(major1) + (6034256072597807/100000000000000 : ℝ)*(major2) + (2826235553/100000000000000 : ℝ)*(sp0) + (5318141579/100000000000000 : ℝ)*(sp3) + (8084137174842319/100000000000000 : ℝ)*(sp4) + (8084140102361447/100000000000000 : ℝ)*(sp5) + (2021034931705017/25000000000000 : ℝ)*(sp6) + (3984366618167411/100000000000000 : ℝ)*(sp7) + (398437193630899/10000000000000 : ℝ)*(f.failure) + (8084140102361447/100000000000000 : ℝ)*(f.sum) + (40841659166317/13380000000000000000000000000 : ℝ)*base65 + (1030201018942324073/1338000000000000000000000000000000 : ℝ)*base68 + (16346563396222324073/1338000000000000000000000000000000 : ℝ)*base70 + (15691939869046324073/1338000000000000000000000000000000 : ℝ)*base72 + (54881523400163/13380000000000000000000000000 : ℝ)*base74 + (13072201055068324073/1338000000000000000000000000000000 : ℝ)*base76 + (36524936619562324073/1338000000000000000000000000000000 : ℝ)*base78 + (3533482507261675927/1338000000000000000000000000000000 : ℝ)*base79 + (114017184662663/13380000000000000000000000000 : ℝ)*base82 + (525793/62500000000000000000 : ℝ)*base89 + (525793/62500000000000000000 : ℝ)*base91 + (525793/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1243_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1243_s7_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-529875901/2500000000 : ℝ)*x 0 + (5391174367/10000000000 : ℝ)*x 1 + (2633615599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529875901/2500000000 : ℝ)^2109 ≤ (12889143873171/100000000000000 : ℝ)^1597 := by
    have hnat : (529875901 : ℕ)^2109*100000000000000^1597 ≤ 12889143873171^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529875901 2500000000 12889143873171 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391174367/10000000000 : ℝ)^2109 ≤ (44224279605997/100000000000000 : ℝ)^1597 := by
    have hnat : (5391174367 : ℕ)^2109*100000000000000^1597 ≤ 44224279605997^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391174367 10000000000 44224279605997 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633615599/5000000000 : ℝ)^2109 ≤ (1072164412489/2500000000000 : ℝ)^1597 := by
    have hnat : (2633615599 : ℕ)^2109*2500000000000^1597 ≤ 1072164412489^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633615599 5000000000 1072164412489 2500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529875901/2500000000 : ℝ), (5391174367/10000000000 : ℝ), (2633615599/5000000000 : ℝ)] ![(12889143873171/100000000000000 : ℝ), (44224279605997/100000000000000 : ℝ), (1072164412489/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529875901/2500000000 : ℝ)|^2109 ≤ (12889143873171/100000000000000 : ℝ)^1597
        have hw : |(-529875901/2500000000 : ℝ)|=(529875901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391174367/10000000000 : ℝ)|^2109 ≤ (44224279605997/100000000000000 : ℝ)^1597
        have hw : |(5391174367/10000000000 : ℝ)|=(5391174367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633615599/5000000000 : ℝ)|^2109 ≤ (1072164412489/2500000000000 : ℝ)^1597
        have hw : |(2633615599/5000000000 : ℝ)|=(2633615599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668037763/1250000000 : ℝ)*x 0 + (-27279353/125000000 : ℝ)*x 1 + (1316807327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668037763/1250000000 : ℝ)^2109 ≤ (21858610545419/50000000000000 : ℝ)^1597 := by
    have hnat : (668037763 : ℕ)^2109*50000000000000^1597 ≤ 21858610545419^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668037763 1250000000 21858610545419 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27279353/125000000 : ℝ)^2109 ≤ (6698111353/50000000000 : ℝ)^1597 := by
    have hnat : (27279353 : ℕ)^2109*50000000000^1597 ≤ 6698111353^1597*125000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27279353 125000000 6698111353 50000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316807327/2500000000 : ℝ)^2109 ≤ (67010244027/156250000000 : ℝ)^1597 := by
    have hnat : (1316807327 : ℕ)^2109*156250000000^1597 ≤ 67010244027^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316807327 2500000000 67010244027 156250000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668037763/1250000000 : ℝ), (-27279353/125000000 : ℝ), (1316807327/2500000000 : ℝ)] ![(21858610545419/50000000000000 : ℝ), (6698111353/50000000000 : ℝ), (67010244027/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668037763/1250000000 : ℝ)|^2109 ≤ (21858610545419/50000000000000 : ℝ)^1597
        have hw : |(668037763/1250000000 : ℝ)|=(668037763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27279353/125000000 : ℝ)|^2109 ≤ (6698111353/50000000000 : ℝ)^1597
        have hw : |(-27279353/125000000 : ℝ)|=(27279353/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316807327/2500000000 : ℝ)|^2109 ≤ (67010244027/156250000000 : ℝ)^1597
        have hw : |(1316807327/2500000000 : ℝ)|=(1316807327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344301767/10000000000 : ℝ)*x 0 + (5267231053/10000000000 : ℝ)*x 1 + (-2182346377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344301767/10000000000 : ℝ)^2109 ≤ (43717217450321/100000000000000 : ℝ)^1597 := by
    have hnat : (5344301767 : ℕ)^2109*100000000000000^1597 ≤ 43717217450321^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344301767 10000000000 43717217450321 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267231053/10000000000 : ℝ)^2109 ≤ (42886574940443/100000000000000 : ℝ)^1597 := by
    have hnat : (5267231053 : ℕ)^2109*100000000000000^1597 ≤ 42886574940443^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267231053 10000000000 42886574940443 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182346377/10000000000 : ℝ)^2109 ≤ (13396207603711/100000000000000 : ℝ)^1597 := by
    have hnat : (2182346377 : ℕ)^2109*100000000000000^1597 ≤ 13396207603711^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182346377 10000000000 13396207603711 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344301767/10000000000 : ℝ), (5267231053/10000000000 : ℝ), (-2182346377/10000000000 : ℝ)] ![(43717217450321/100000000000000 : ℝ), (42886574940443/100000000000000 : ℝ), (13396207603711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344301767/10000000000 : ℝ)|^2109 ≤ (43717217450321/100000000000000 : ℝ)^1597
        have hw : |(5344301767/10000000000 : ℝ)|=(5344301767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267231053/10000000000 : ℝ)|^2109 ≤ (42886574940443/100000000000000 : ℝ)^1597
        have hw : |(5267231053/10000000000 : ℝ)|=(5267231053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182346377/10000000000 : ℝ)|^2109 ≤ (13396207603711/100000000000000 : ℝ)^1597
        have hw : |(-2182346377/10000000000 : ℝ)|=(2182346377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350637061/10000000000 : ℝ)*x 0 + (4226661683/10000000000 : ℝ)*x 1 + (2239071087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350637061/10000000000 : ℝ)^2109 ≤ (33317506645699/100000000000000 : ℝ)^1597 := by
    have hnat : (4350637061 : ℕ)^2109*100000000000000^1597 ≤ 33317506645699^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350637061 10000000000 33317506645699 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226661683/10000000000 : ℝ)^2109 ≤ (16034737838883/50000000000000 : ℝ)^1597 := by
    have hnat : (4226661683 : ℕ)^2109*50000000000000^1597 ≤ 16034737838883^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226661683 10000000000 16034737838883 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239071087/5000000000 : ℝ)^2109 ≤ (17306508829667/50000000000000 : ℝ)^1597 := by
    have hnat : (2239071087 : ℕ)^2109*50000000000000^1597 ≤ 17306508829667^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239071087 5000000000 17306508829667 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350637061/10000000000 : ℝ), (4226661683/10000000000 : ℝ), (2239071087/5000000000 : ℝ)] ![(33317506645699/100000000000000 : ℝ), (16034737838883/50000000000000 : ℝ), (17306508829667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350637061/10000000000 : ℝ)|^2109 ≤ (33317506645699/100000000000000 : ℝ)^1597
        have hw : |(4350637061/10000000000 : ℝ)|=(4350637061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226661683/10000000000 : ℝ)|^2109 ≤ (16034737838883/50000000000000 : ℝ)^1597
        have hw : |(4226661683/10000000000 : ℝ)|=(4226661683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239071087/5000000000 : ℝ)|^2109 ≤ (17306508829667/50000000000000 : ℝ)^1597
        have hw : |(2239071087/5000000000 : ℝ)|=(2239071087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119508351/10000000000 : ℝ)*x 0 + (2633771537/5000000000 : ℝ)*x 1 + (1347715321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119508351/10000000000 : ℝ)^2109 ≤ (2577836399127/20000000000000 : ℝ)^1597 := by
    have hnat : (2119508351 : ℕ)^2109*20000000000000^1597 ≤ 2577836399127^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119508351 10000000000 2577836399127 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633771537/5000000000 : ℝ)^2109 ≤ (42889929987423/100000000000000 : ℝ)^1597 := by
    have hnat : (2633771537 : ℕ)^2109*100000000000000^1597 ≤ 42889929987423^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633771537 5000000000 42889929987423 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347715321/2500000000 : ℝ)^2109 ≤ (22110444003509/50000000000000 : ℝ)^1597 := by
    have hnat : (1347715321 : ℕ)^2109*50000000000000^1597 ≤ 22110444003509^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347715321 2500000000 22110444003509 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119508351/10000000000 : ℝ), (2633771537/5000000000 : ℝ), (1347715321/2500000000 : ℝ)] ![(2577836399127/20000000000000 : ℝ), (42889929987423/100000000000000 : ℝ), (22110444003509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119508351/10000000000 : ℝ)|^2109 ≤ (2577836399127/20000000000000 : ℝ)^1597
        have hw : |(-2119508351/10000000000 : ℝ)|=(2119508351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633771537/5000000000 : ℝ)|^2109 ≤ (42889929987423/100000000000000 : ℝ)^1597
        have hw : |(2633771537/5000000000 : ℝ)|=(2633771537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347715321/2500000000 : ℝ)|^2109 ≤ (22110444003509/50000000000000 : ℝ)^1597
        have hw : |(1347715321/2500000000 : ℝ)|=(1347715321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312674181/10000000000 : ℝ)*x 0 + (-2058716311/10000000000 : ℝ)*x 1 + (134771543/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312674181/10000000000 : ℝ)^2109 ≤ (10843969496797/25000000000000 : ℝ)^1597 := by
    have hnat : (5312674181 : ℕ)^2109*25000000000000^1597 ≤ 10843969496797^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312674181 10000000000 10843969496797 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058716311/10000000000 : ℝ)^2109 ≤ (496129170579/4000000000000 : ℝ)^1597 := by
    have hnat : (2058716311 : ℕ)^2109*4000000000000^1597 ≤ 496129170579^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058716311 10000000000 496129170579 4000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134771543/250000000 : ℝ)^2109 ≤ (44220892730121/100000000000000 : ℝ)^1597 := by
    have hnat : (134771543 : ℕ)^2109*100000000000000^1597 ≤ 44220892730121^1597*250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134771543 250000000 44220892730121 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312674181/10000000000 : ℝ), (-2058716311/10000000000 : ℝ), (134771543/250000000 : ℝ)] ![(10843969496797/25000000000000 : ℝ), (496129170579/4000000000000 : ℝ), (44220892730121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312674181/10000000000 : ℝ)|^2109 ≤ (10843969496797/25000000000000 : ℝ)^1597
        have hw : |(5312674181/10000000000 : ℝ)|=(5312674181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058716311/10000000000 : ℝ)|^2109 ≤ (496129170579/4000000000000 : ℝ)^1597
        have hw : |(-2058716311/10000000000 : ℝ)|=(2058716311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134771543/250000000 : ℝ)|^2109 ≤ (44220892730121/100000000000000 : ℝ)^1597
        have hw : |(134771543/250000000 : ℝ)|=(134771543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312674093/10000000000 : ℝ)*x 0 + (5390861931/10000000000 : ℝ)*x 1 + (-2058716143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312674093/10000000000 : ℝ)^2109 ≤ (8675175407671/20000000000000 : ℝ)^1597 := by
    have hnat : (5312674093 : ℕ)^2109*20000000000000^1597 ≤ 8675175407671^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312674093 10000000000 8675175407671 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390861931/10000000000 : ℝ)^2109 ≤ (44220895015843/100000000000000 : ℝ)^1597 := by
    have hnat : (5390861931 : ℕ)^2109*100000000000000^1597 ≤ 44220895015843^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390861931 10000000000 44220895015843 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058716143/10000000000 : ℝ)^2109 ≤ (12403227927821/100000000000000 : ℝ)^1597 := by
    have hnat : (2058716143 : ℕ)^2109*100000000000000^1597 ≤ 12403227927821^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058716143 10000000000 12403227927821 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312674093/10000000000 : ℝ), (5390861931/10000000000 : ℝ), (-2058716143/10000000000 : ℝ)] ![(8675175407671/20000000000000 : ℝ), (44220895015843/100000000000000 : ℝ), (12403227927821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312674093/10000000000 : ℝ)|^2109 ≤ (8675175407671/20000000000000 : ℝ)^1597
        have hw : |(5312674093/10000000000 : ℝ)|=(5312674093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390861931/10000000000 : ℝ)|^2109 ≤ (44220895015843/100000000000000 : ℝ)^1597
        have hw : |(5390861931/10000000000 : ℝ)|=(5390861931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058716143/10000000000 : ℝ)|^2109 ≤ (12403227927821/100000000000000 : ℝ)^1597
        have hw : |(-2058716143/10000000000 : ℝ)|=(2058716143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s7_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350645617/10000000000 : ℝ)*x 0 + (4477507983/10000000000 : ℝ)*x 1 + (4227299069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350645617/10000000000 : ℝ)^2109 ≤ (8329398293701/25000000000000 : ℝ)^1597 := by
    have hnat : (4350645617 : ℕ)^2109*25000000000000^1597 ≤ 8329398293701^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350645617 10000000000 8329398293701 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477507983/10000000000 : ℝ)^2109 ≤ (6921308878633/20000000000000 : ℝ)^1597 := by
    have hnat : (4477507983 : ℕ)^2109*20000000000000^1597 ≤ 6921308878633^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477507983 10000000000 6921308878633 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227299069/10000000000 : ℝ)^2109 ≤ (8018965603771/25000000000000 : ℝ)^1597 := by
    have hnat : (4227299069 : ℕ)^2109*25000000000000^1597 ≤ 8018965603771^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227299069 10000000000 8018965603771 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350645617/10000000000 : ℝ), (4477507983/10000000000 : ℝ), (4227299069/10000000000 : ℝ)] ![(8329398293701/25000000000000 : ℝ), (6921308878633/20000000000000 : ℝ), (8018965603771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350645617/10000000000 : ℝ)|^2109 ≤ (8329398293701/25000000000000 : ℝ)^1597
        have hw : |(4350645617/10000000000 : ℝ)|=(4350645617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477507983/10000000000 : ℝ)|^2109 ≤ (6921308878633/20000000000000 : ℝ)^1597
        have hw : |(4477507983/10000000000 : ℝ)|=(4477507983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227299069/10000000000 : ℝ)|^2109 ≤ (8018965603771/25000000000000 : ℝ)^1597
        have hw : |(4227299069/10000000000 : ℝ)|=(4227299069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11479/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (459/4000 : ℝ) ^ (8435/2048 : ℝ) ≤ (2682120131934813/20000000000000000000 : ℝ) := by
    have hpowers : (459/4000 : ℝ)^8435 ≤ (2682120131934813/20000000000000000000 : ℝ)^2048 := by
      have hnat : (459 : ℕ)^8435*20000000000000000000^2048 ≤ 2682120131934813^2048*4000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 4000 2682120131934813 20000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/4000 : ℝ)) (X := (2682120131934813/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (31410197604575613/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^8435 ≤ (31410197604575613/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14109 : ℕ)^8435*100000000000000000000^2048 ≤ 31410197604575613^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 31410197604575613 100000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (31410197604575613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002682120131934813/10000000000000000000 : ℝ) ≤ (1000065114692721/1000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (10002682120131934813/10000000000000000000 : ℝ)^2048 ≤ (1000065114692721/1000000000000000 : ℝ)^8435 := by
      have hnat : (10002682120131934813 : ℕ)^2048*1000000000000000^8435 ≤ 1000065114692721^8435*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002682120131934813 10000000000000000000 1000065114692721 1000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000065114692721/1000000000000000 : ℝ)) (X := (10002682120131934813/10000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022410399132124839/50000000000000000000 : ℝ) ≤ (2500272013700043/2500000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50022410399132124839/50000000000000000000 : ℝ)^2048 ≤ (2500272013700043/2500000000000000 : ℝ)^8435 := by
      have hnat : (50022410399132124839 : ℕ)^2048*2500000000000000^8435 ≤ 2500272013700043^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022410399132124839 50000000000000000000 2500272013700043 2500000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500272013700043/2500000000000000 : ℝ)) (X := (50022410399132124839/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031410197604575613/50000000000000000000 : ℝ) ≤ (5000762481336567/5000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50031410197604575613/50000000000000000000 : ℝ)^2048 ≤ (5000762481336567/5000000000000000 : ℝ)^8435 := by
      have hnat : (50031410197604575613 : ℕ)^2048*5000000000000000^8435 ≤ 5000762481336567^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031410197604575613 50000000000000000000 5000762481336567 5000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000762481336567/5000000000000000 : ℝ)) (X := (50031410197604575613/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2682120131934813/20000000000000000000 : ℝ) ≤ ((219430734044348277/219500000000000000 : ℝ)+2*(72817978827/43900000000000 : ℝ)*(459/4000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (219430734044348277/219500000000000000 : ℝ)+2*(72817978827/43900000000000 : ℝ)*(459/4000 : ℝ)=(1000065114692721/1000000000000000 : ℝ) by norm_num, show 1+2*(2682120131934813/20000000000000000000 : ℝ)=(10002682120131934813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31410197604575613/100000000000000000000 : ℝ)+(2682120131934813/20000000000000000000 : ℝ) ≤ ((219430734044348277/219500000000000000 : ℝ)+(72817978827/43900000000000 : ℝ)*((14109/100000 : ℝ)+(459/4000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (219430734044348277/219500000000000000 : ℝ)+(72817978827/43900000000000 : ℝ)*((14109/100000 : ℝ)+(459/4000 : ℝ))=(2500272013700043/2500000000000000 : ℝ) by norm_num, show 1+(31410197604575613/100000000000000000000 : ℝ)+(2682120131934813/20000000000000000000 : ℝ)=(50022410399132124839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31410197604575613/100000000000000000000 : ℝ) ≤ ((219430734044348277/219500000000000000 : ℝ)+2*(72817978827/43900000000000 : ℝ)*(14109/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (219430734044348277/219500000000000000 : ℝ)+2*(72817978827/43900000000000 : ℝ)*(14109/100000 : ℝ)=(5000762481336567/5000000000000000 : ℝ) by norm_num, show 1+2*(31410197604575613/100000000000000000000 : ℝ)=(50031410197604575613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (219430734044348277/219500000000000000 : ℝ)*(X 1 0+X 2 0)+(72817978827/43900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (219430734044348277/219500000000000000 : ℝ)) (alpha := (72817978827/43900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (219430734044348277/219500000000000000 : ℝ)*(X 0 1+X 2 1)+(72817978827/43900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (219430734044348277/219500000000000000 : ℝ)) (alpha := (72817978827/43900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (219430734044348277/219500000000000000 : ℝ)*(X 0 2+X 1 2)+(72817978827/43900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (219430734044348277/219500000000000000 : ℝ)) (alpha := (72817978827/43900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529875901/2500000000 : ℝ)*X 0 0+(5391174367/10000000000 : ℝ)*X 0 1+(2633615599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668037763/1250000000 : ℝ)*X 1 0+(-27279353/125000000 : ℝ)*X 1 1+(1316807327/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344301767/10000000000 : ℝ)*X 2 0+(5267231053/10000000000 : ℝ)*X 2 1+(-2182346377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350637061/10000000000 : ℝ)*X 0 0+(4226661683/10000000000 : ℝ)*X 0 1+(2239071087/5000000000 : ℝ)*X 0 2+(4350637061/10000000000 : ℝ)*X 1 0+(4226661683/10000000000 : ℝ)*X 1 1+(2239071087/5000000000 : ℝ)*X 1 2+(4350637061/10000000000 : ℝ)*X 2 0+(4226661683/10000000000 : ℝ)*X 2 1+(2239071087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119508351/10000000000 : ℝ)*X 0 0+(2633771537/5000000000 : ℝ)*X 0 1+(1347715321/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312674181/10000000000 : ℝ)*X 1 0+(-2058716311/10000000000 : ℝ)*X 1 1+(134771543/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312674093/10000000000 : ℝ)*X 2 0+(5390861931/10000000000 : ℝ)*X 2 1+(-2058716143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350645617/10000000000 : ℝ)*X 0 0+(4477507983/10000000000 : ℝ)*X 0 1+(4227299069/10000000000 : ℝ)*X 0 2+(4350645617/10000000000 : ℝ)*X 1 0+(4477507983/10000000000 : ℝ)*X 1 1+(4227299069/10000000000 : ℝ)*X 1 2+(4350645617/10000000000 : ℝ)*X 2 0+(4477507983/10000000000 : ℝ)*X 2 1+(4227299069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145875367386341421900420507/10975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1160368747/50000000000000 : ℝ)*(base19) + (5313221/1562500000000 : ℝ)*(base23) + (95309437/10000000000000 : ℝ)*(lower2) + (203397387/50000000000000 : ℝ)*(upper5) + (6022360157819999/100000000000000 : ℝ)*(major0) + (6022360157819999/100000000000000 : ℝ)*(major1) + (6022360157819999/100000000000000 : ℝ)*(major2) + (8068184587639881/100000000000000 : ℝ)*(sp0) + (8068147766705107/100000000000000 : ℝ)*(sp1) + (4034101187708289/50000000000000 : ℝ)*(sp2) + (994121006668929/25000000000000 : ℝ)*(sp3) + (18127822841/100000000000000 : ℝ)*(sp4) + (26314010061/50000000000000 : ℝ)*(sp5) + (33130448039/100000000000000 : ℝ)*(sp7) + (1988258578561877/50000000000000 : ℝ)*(f.failure) + (4034101357731361/50000000000000 : ℝ)*(f.sum) + (9899454424507/2195000000000000000000000000 : ℝ)*base66 + (346047856088043277/21950000000000000000000000000000 : ℝ)*base68 + (8929848538493277/21950000000000000000000000000000 : ℝ)*base70 + (105360662992893277/21950000000000000000000000000000 : ℝ)*base72 + (638384563089/274375000000000000000000000 : ℝ)*base74 + (845514819320793277/21950000000000000000000000000000 : ℝ)*base76 + (355173132639093277/21950000000000000000000000000000 : ℝ)*base78 + (766827448040393277/21950000000000000000000000000000 : ℝ)*base80 + (3409446264391/1097500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (198361/312500000000000000000 : ℝ)*base90 + (198361/312500000000000000000 : ℝ)*base92 + (198361/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38065756403638786844817021/10975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254277649/50000000000000 : ℝ)*(base8) + (28225219/20000000000000 : ℝ)*(base15) + (174550083/50000000000000 : ℝ)*(base29) + (182007973/50000000000000 : ℝ)*(upper3) + (28712701/50000000000000 : ℝ)*(lower4) + (19986491/50000000000000 : ℝ)*(upper5) + (6052873169819509/100000000000000 : ℝ)*(major0) + (242114940756787/4000000000000 : ℝ)*(major1) + (242114940756787/4000000000000 : ℝ)*(major2) + (25321152823/100000000000000 : ℝ)*(sp2) + (8109081523638949/100000000000000 : ℝ)*(sp4) + (4054540770983993/50000000000000 : ℝ)*(sp5) + (4054528180970629/50000000000000 : ℝ)*(sp6) + (3996664890031561/100000000000000 : ℝ)*(sp7) + (3996664890031561/100000000000000 : ℝ)*(f.failure) + (8109082032194247/100000000000000 : ℝ)*(f.sum) + (3861305517437/439000000000000000000000000 : ℝ)*base66 + (4453246798808999/878000000000000000000000000000 : ℝ)*base67 + (2813104499799001/878000000000000000000000000000 : ℝ)*base70 + (558355375345410993/21950000000000000000000000000000 : ℝ)*base71 + (6130824209731/2195000000000000000000000000 : ℝ)*base74 + (617882198432599/878000000000000000000000000000 : ℝ)*base75 + (342156704315860993/21950000000000000000000000000000 : ℝ)*base77 + (1561928973145401/878000000000000000000000000000 : ℝ)*base80 + (848402914313/274375000000000000000000000 : ℝ)*base81 + (2116427/625000000000000000000 : ℝ)*base89 + (2116427/625000000000000000000 : ℝ)*base91 + (2116427/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1243_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1243_s8_0 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059753431/5000000000 : ℝ)*x 0 + (5391137951/10000000000 : ℝ)*x 1 + (2633632727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059753431/5000000000 : ℝ)^2109 ≤ (1288917003769/10000000000000 : ℝ)^1597 := by
    have hnat : (1059753431 : ℕ)^2109*10000000000000^1597 ≤ 1288917003769^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059753431 5000000000 1288917003769 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391137951/10000000000 : ℝ)^2109 ≤ (690998204869/1562500000000 : ℝ)^1597 := by
    have hnat : (5391137951 : ℕ)^2109*1562500000000^1597 ≤ 690998204869^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391137951 10000000000 690998204869 1562500000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633632727/5000000000 : ℝ)^2109 ≤ (4288694483861/10000000000000 : ℝ)^1597 := by
    have hnat : (2633632727 : ℕ)^2109*10000000000000^1597 ≤ 4288694483861^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633632727 5000000000 4288694483861 10000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059753431/5000000000 : ℝ), (5391137951/10000000000 : ℝ), (2633632727/5000000000 : ℝ)] ![(1288917003769/10000000000000 : ℝ), (690998204869/1562500000000 : ℝ), (4288694483861/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059753431/5000000000 : ℝ)|^2109 ≤ (1288917003769/10000000000000 : ℝ)^1597
        have hw : |(-1059753431/5000000000 : ℝ)|=(1059753431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391137951/10000000000 : ℝ)|^2109 ≤ (690998204869/1562500000000 : ℝ)^1597
        have hw : |(5391137951/10000000000 : ℝ)|=(5391137951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633632727/5000000000 : ℝ)|^2109 ≤ (4288694483861/10000000000000 : ℝ)^1597
        have hw : |(2633632727/5000000000 : ℝ)|=(2633632727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_1 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336073169/2500000000 : ℝ)*x 0 + (-2182312631/10000000000 : ℝ)*x 1 + (5267265627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336073169/2500000000 : ℝ)^2109 ≤ (43717119242801/100000000000000 : ℝ)^1597 := by
    have hnat : (1336073169 : ℕ)^2109*100000000000000^1597 ≤ 43717119242801^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336073169 2500000000 43717119242801 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182312631/10000000000 : ℝ)^2109 ≤ (3348983511167/25000000000000 : ℝ)^1597 := by
    have hnat : (2182312631 : ℕ)^2109*25000000000000^1597 ≤ 3348983511167^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182312631 10000000000 3348983511167 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267265627/10000000000 : ℝ)^2109 ≤ (21443473349401/50000000000000 : ℝ)^1597 := by
    have hnat : (5267265627 : ℕ)^2109*50000000000000^1597 ≤ 21443473349401^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267265627 10000000000 21443473349401 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336073169/2500000000 : ℝ), (-2182312631/10000000000 : ℝ), (5267265627/10000000000 : ℝ)] ![(43717119242801/100000000000000 : ℝ), (3348983511167/25000000000000 : ℝ), (21443473349401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336073169/2500000000 : ℝ)|^2109 ≤ (43717119242801/100000000000000 : ℝ)^1597
        have hw : |(1336073169/2500000000 : ℝ)|=(1336073169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182312631/10000000000 : ℝ)|^2109 ≤ (3348983511167/25000000000000 : ℝ)^1597
        have hw : |(-2182312631/10000000000 : ℝ)|=(2182312631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267265627/10000000000 : ℝ)|^2109 ≤ (21443473349401/50000000000000 : ℝ)^1597
        have hw : |(5267265627/10000000000 : ℝ)|=(5267265627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_2 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672146499/5000000000 : ℝ)*x 0 + (658408173/1250000000 : ℝ)*x 1 + (-545578131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672146499/5000000000 : ℝ)^2109 ≤ (10929280680319/25000000000000 : ℝ)^1597 := by
    have hnat : (2672146499 : ℕ)^2109*25000000000000^1597 ≤ 10929280680319^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672146499 5000000000 10929280680319 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658408173/1250000000 : ℝ)^2109 ≤ (10721736021483/25000000000000 : ℝ)^1597 := by
    have hnat : (658408173 : ℕ)^2109*25000000000000^1597 ≤ 10721736021483^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658408173 1250000000 10721736021483 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545578131/2500000000 : ℝ)^2109 ≤ (3348983294321/25000000000000 : ℝ)^1597 := by
    have hnat : (545578131 : ℕ)^2109*25000000000000^1597 ≤ 3348983294321^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545578131 2500000000 3348983294321 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672146499/5000000000 : ℝ), (658408173/1250000000 : ℝ), (-545578131/2500000000 : ℝ)] ![(10929280680319/25000000000000 : ℝ), (10721736021483/25000000000000 : ℝ), (3348983294321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672146499/5000000000 : ℝ)|^2109 ≤ (10929280680319/25000000000000 : ℝ)^1597
        have hw : |(2672146499/5000000000 : ℝ)|=(2672146499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658408173/1250000000 : ℝ)|^2109 ≤ (10721736021483/25000000000000 : ℝ)^1597
        have hw : |(658408173/1250000000 : ℝ)|=(658408173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545578131/2500000000 : ℝ)|^2109 ≤ (3348983294321/25000000000000 : ℝ)^1597
        have hw : |(-545578131/2500000000 : ℝ)|=(545578131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_3 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350638257/10000000000 : ℝ)*x 0 + (2113367821/5000000000 : ℝ)*x 1 + (1119517097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350638257/10000000000 : ℝ)^2109 ≤ (16658759370581/50000000000000 : ℝ)^1597 := by
    have hnat : (4350638257 : ℕ)^2109*50000000000000^1597 ≤ 16658759370581^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350638257 10000000000 16658759370581 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113367821/5000000000 : ℝ)^2109 ≤ (32070216746149/100000000000000 : ℝ)^1597 := by
    have hnat : (2113367821 : ℕ)^2109*100000000000000^1597 ≤ 32070216746149^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113367821 5000000000 32070216746149 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119517097/2500000000 : ℝ)^2109 ≤ (17306132250687/50000000000000 : ℝ)^1597 := by
    have hnat : (1119517097 : ℕ)^2109*50000000000000^1597 ≤ 17306132250687^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119517097 2500000000 17306132250687 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350638257/10000000000 : ℝ), (2113367821/5000000000 : ℝ), (1119517097/2500000000 : ℝ)] ![(16658759370581/50000000000000 : ℝ), (32070216746149/100000000000000 : ℝ), (17306132250687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350638257/10000000000 : ℝ)|^2109 ≤ (16658759370581/50000000000000 : ℝ)^1597
        have hw : |(4350638257/10000000000 : ℝ)|=(4350638257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113367821/5000000000 : ℝ)|^2109 ≤ (32070216746149/100000000000000 : ℝ)^1597
        have hw : |(2113367821/5000000000 : ℝ)|=(2113367821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119517097/2500000000 : ℝ)|^2109 ≤ (17306132250687/50000000000000 : ℝ)^1597
        have hw : |(1119517097/2500000000 : ℝ)|=(1119517097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_4 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-529877903/2500000000 : ℝ)*x 0 + (5267577689/10000000000 : ℝ)*x 1 + (5390824507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529877903/2500000000 : ℝ)^2109 ≤ (2577841636853/20000000000000 : ℝ)^1597 := by
    have hnat : (529877903 : ℕ)^2109*20000000000000^1597 ≤ 2577841636853^1597*2500000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529877903 2500000000 2577841636853 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267577689/10000000000 : ℝ)^2109 ≤ (8578060438741/20000000000000 : ℝ)^1597 := by
    have hnat : (5267577689 : ℕ)^2109*20000000000000^1597 ≤ 8578060438741^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267577689 10000000000 8578060438741 20000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390824507/10000000000 : ℝ)^2109 ≤ (22110244804673/50000000000000 : ℝ)^1597 := by
    have hnat : (5390824507 : ℕ)^2109*50000000000000^1597 ≤ 22110244804673^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390824507 10000000000 22110244804673 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529877903/2500000000 : ℝ), (5267577689/10000000000 : ℝ), (5390824507/10000000000 : ℝ)] ![(2577841636853/20000000000000 : ℝ), (8578060438741/20000000000000 : ℝ), (22110244804673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529877903/2500000000 : ℝ)|^2109 ≤ (2577841636853/20000000000000 : ℝ)^1597
        have hw : |(-529877903/2500000000 : ℝ)|=(529877903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267577689/10000000000 : ℝ)|^2109 ≤ (8578060438741/20000000000000 : ℝ)^1597
        have hw : |(5267577689/10000000000 : ℝ)|=(5267577689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390824507/10000000000 : ℝ)|^2109 ≤ (22110244804673/50000000000000 : ℝ)^1597
        have hw : |(5390824507/10000000000 : ℝ)|=(5390824507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_5 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312684109/10000000000 : ℝ)*x 0 + (-2058753331/10000000000 : ℝ)*x 1 + (673853081/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312684109/10000000000 : ℝ)^2109 ≤ (10843996258187/25000000000000 : ℝ)^1597 := by
    have hnat : (5312684109 : ℕ)^2109*25000000000000^1597 ≤ 10843996258187^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312684109 10000000000 10843996258187 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058753331/10000000000 : ℝ)^2109 ≤ (12403523806723/100000000000000 : ℝ)^1597 := by
    have hnat : (2058753331 : ℕ)^2109*100000000000000^1597 ≤ 12403523806723^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058753331 10000000000 12403523806723 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673853081/1250000000 : ℝ)^2109 ≤ (44220491136769/100000000000000 : ℝ)^1597 := by
    have hnat : (673853081 : ℕ)^2109*100000000000000^1597 ≤ 44220491136769^1597*1250000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673853081 1250000000 44220491136769 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312684109/10000000000 : ℝ), (-2058753331/10000000000 : ℝ), (673853081/1250000000 : ℝ)] ![(10843996258187/25000000000000 : ℝ), (12403523806723/100000000000000 : ℝ), (44220491136769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312684109/10000000000 : ℝ)|^2109 ≤ (10843996258187/25000000000000 : ℝ)^1597
        have hw : |(5312684109/10000000000 : ℝ)|=(5312684109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058753331/10000000000 : ℝ)|^2109 ≤ (12403523806723/100000000000000 : ℝ)^1597
        have hw : |(-2058753331/10000000000 : ℝ)|=(2058753331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673853081/1250000000 : ℝ)|^2109 ≤ (44220491136769/100000000000000 : ℝ)^1597
        have hw : |(673853081/1250000000 : ℝ)|=(673853081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_6 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312684287/10000000000 : ℝ)*x 0 + (336926527/625000000 : ℝ)*x 1 + (-411750677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312684287/10000000000 : ℝ)^2109 ≤ (21687993475989/50000000000000 : ℝ)^1597 := by
    have hnat : (5312684287 : ℕ)^2109*50000000000000^1597 ≤ 21687993475989^1597*10000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312684287 10000000000 21687993475989 50000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336926527/625000000 : ℝ)^2109 ≤ (5527561099611/12500000000000 : ℝ)^1597 := by
    have hnat : (336926527 : ℕ)^2109*12500000000000^1597 ≤ 5527561099611^1597*625000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336926527 625000000 5527561099611 12500000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411750677/2000000000 : ℝ)^2109 ≤ (3100881059091/25000000000000 : ℝ)^1597 := by
    have hnat : (411750677 : ℕ)^2109*25000000000000^1597 ≤ 3100881059091^1597*2000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411750677 2000000000 3100881059091 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312684287/10000000000 : ℝ), (336926527/625000000 : ℝ), (-411750677/2000000000 : ℝ)] ![(21687993475989/50000000000000 : ℝ), (5527561099611/12500000000000 : ℝ), (3100881059091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312684287/10000000000 : ℝ)|^2109 ≤ (21687993475989/50000000000000 : ℝ)^1597
        have hw : |(5312684287/10000000000 : ℝ)|=(5312684287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336926527/625000000 : ℝ)|^2109 ≤ (5527561099611/12500000000000 : ℝ)^1597
        have hw : |(336926527/625000000 : ℝ)|=(336926527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411750677/2000000000 : ℝ)|^2109 ≤ (3100881059091/25000000000000 : ℝ)^1597
        have hw : |(-411750677/2000000000 : ℝ)|=(411750677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1243_s8_7 (p : ℝ) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174025897/400000000 : ℝ)*x 0 + (2238717539/5000000000 : ℝ)*x 1 + (2113685753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174025897/400000000 : ℝ)^2109 ≤ (8329402864899/25000000000000 : ℝ)^1597 := by
    have hnat : (174025897 : ℕ)^2109*25000000000000^1597 ≤ 8329402864899^1597*400000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174025897 400000000 8329402864899 25000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238717539/5000000000 : ℝ)^2109 ≤ (34605800261627/100000000000000 : ℝ)^1597 := by
    have hnat : (2238717539 : ℕ)^2109*100000000000000^1597 ≤ 34605800261627^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238717539 5000000000 34605800261627 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113685753/5000000000 : ℝ)^2109 ≤ (32076588268091/100000000000000 : ℝ)^1597 := by
    have hnat : (2113685753 : ℕ)^2109*100000000000000^1597 ≤ 32076588268091^1597*5000000000^2109 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113685753 5000000000 32076588268091 100000000000000 2109 1597 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2109/512 : ℝ)) 2109 1597 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174025897/400000000 : ℝ), (2238717539/5000000000 : ℝ), (2113685753/5000000000 : ℝ)] ![(8329402864899/25000000000000 : ℝ), (34605800261627/100000000000000 : ℝ), (32076588268091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174025897/400000000 : ℝ)|^2109 ≤ (8329402864899/25000000000000 : ℝ)^1597
        have hw : |(174025897/400000000 : ℝ)|=(174025897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238717539/5000000000 : ℝ)|^2109 ≤ (34605800261627/100000000000000 : ℝ)^1597
        have hw : |(2238717539/5000000000 : ℝ)|=(2238717539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113685753/5000000000 : ℝ)|^2109 ≤ (32076588268091/100000000000000 : ℝ)^1597
        have hw : |(2113685753/5000000000 : ℝ)|=(2113685753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1243_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (287/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11479/100000 : ℝ) ^ (8435/2048 : ℝ) ≤ (2685972934150643/20000000000000000000 : ℝ) := by
    have hpowers : (11479/100000 : ℝ)^8435 ≤ (2685972934150643/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11479 : ℕ)^8435*20000000000000000000^2048 ≤ 2685972934150643^2048*100000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11479 100000 2685972934150643 20000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11479/100000 : ℝ)) (X := (2685972934150643/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (8435/2048 : ℝ) ≤ (31373537173762843/100000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^8435 ≤ (31373537173762843/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8435*100000000000000000000^2048 ≤ 31373537173762843^2048*20000^8435 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 31373537173762843 100000000000000000000 8435 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (31373537173762843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002685972934150643/10000000000000000000 : ℝ) ≤ (10000652082189293/10000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (10002685972934150643/10000000000000000000 : ℝ)^2048 ≤ (10000652082189293/10000000000000000 : ℝ)^8435 := by
      have hnat : (10002685972934150643 : ℕ)^2048*10000000000000000^8435 ≤ 10000652082189293^8435*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002685972934150643 10000000000000000000 10000652082189293 10000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652082189293/10000000000000000 : ℝ)) (X := (10002685972934150643/10000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022401700922258029/50000000000000000000 : ℝ) ≤ (10001087632562079/10000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50022401700922258029/50000000000000000000 : ℝ)^2048 ≤ (10001087632562079/10000000000000000 : ℝ)^8435 := by
      have hnat : (50022401700922258029 : ℕ)^2048*10000000000000000^8435 ≤ 10001087632562079^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022401700922258029 50000000000000000000 10001087632562079 10000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001087632562079/10000000000000000 : ℝ)) (X := (50022401700922258029/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031373537173762843/50000000000000000000 : ℝ) ≤ (2000304636586973/2000000000000000 : ℝ) ^ (8435/2048 : ℝ) := by
    have hpowers : (50031373537173762843/50000000000000000000 : ℝ)^2048 ≤ (2000304636586973/2000000000000000 : ℝ)^8435 := by
      have hnat : (50031373537173762843 : ℕ)^2048*2000000000000000^8435 ≤ 2000304636586973^8435*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031373537173762843 50000000000000000000 2000304636586973 2000000000000000 2048 8435 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000304636586973/2000000000000000 : ℝ)) (X := (50031373537173762843/50000000000000000000 : ℝ)) (by norm_num) 8435 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2685972934150643/20000000000000000000 : ℝ) ≤ ((201936253864389711/202000000000000000 : ℝ)+2*(217775186393/131300000000000 : ℝ)*(11479/100000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (201936253864389711/202000000000000000 : ℝ)+2*(217775186393/131300000000000 : ℝ)*(11479/100000 : ℝ)=(10000652082189293/10000000000000000 : ℝ) by norm_num, show 1+2*(2685972934150643/20000000000000000000 : ℝ)=(10002685972934150643/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31373537173762843/100000000000000000000 : ℝ)+(2685972934150643/20000000000000000000 : ℝ) ≤ ((201936253864389711/202000000000000000 : ℝ)+(217775186393/131300000000000 : ℝ)*((2821/20000 : ℝ)+(11479/100000 : ℝ)))^(8435/2048 : ℝ) := by
    rw [show (201936253864389711/202000000000000000 : ℝ)+(217775186393/131300000000000 : ℝ)*((2821/20000 : ℝ)+(11479/100000 : ℝ))=(10001087632562079/10000000000000000 : ℝ) by norm_num, show 1+(31373537173762843/100000000000000000000 : ℝ)+(2685972934150643/20000000000000000000 : ℝ)=(50022401700922258029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31373537173762843/100000000000000000000 : ℝ) ≤ ((201936253864389711/202000000000000000 : ℝ)+2*(217775186393/131300000000000 : ℝ)*(2821/20000 : ℝ))^(8435/2048 : ℝ) := by
    rw [show (201936253864389711/202000000000000000 : ℝ)+2*(217775186393/131300000000000 : ℝ)*(2821/20000 : ℝ)=(2000304636586973/2000000000000000 : ℝ) by norm_num, show 1+2*(31373537173762843/100000000000000000000 : ℝ)=(50031373537173762843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (201936253864389711/202000000000000000 : ℝ)*(X 1 0+X 2 0)+(217775186393/131300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (201936253864389711/202000000000000000 : ℝ)) (alpha := (217775186393/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (201936253864389711/202000000000000000 : ℝ)*(X 0 1+X 2 1)+(217775186393/131300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (201936253864389711/202000000000000000 : ℝ)) (alpha := (217775186393/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (201936253864389711/202000000000000000 : ℝ)*(X 0 2+X 1 2)+(217775186393/131300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8435/2048 : ℝ)) (lo := (11479/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (201936253864389711/202000000000000000 : ℝ)) (alpha := (217775186393/131300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1059753431/5000000000 : ℝ)*X 0 0+(5391137951/10000000000 : ℝ)*X 0 1+(2633632727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336073169/2500000000 : ℝ)*X 1 0+(-2182312631/10000000000 : ℝ)*X 1 1+(5267265627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672146499/5000000000 : ℝ)*X 2 0+(658408173/1250000000 : ℝ)*X 2 1+(-545578131/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350638257/10000000000 : ℝ)*X 0 0+(2113367821/5000000000 : ℝ)*X 0 1+(1119517097/2500000000 : ℝ)*X 0 2+(4350638257/10000000000 : ℝ)*X 1 0+(2113367821/5000000000 : ℝ)*X 1 1+(1119517097/2500000000 : ℝ)*X 1 2+(4350638257/10000000000 : ℝ)*X 2 0+(2113367821/5000000000 : ℝ)*X 2 1+(1119517097/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529877903/2500000000 : ℝ)*X 0 0+(5267577689/10000000000 : ℝ)*X 0 1+(5390824507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312684109/10000000000 : ℝ)*X 1 0+(-2058753331/10000000000 : ℝ)*X 1 1+(673853081/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312684287/10000000000 : ℝ)*X 2 0+(336926527/625000000 : ℝ)*X 2 1+(-411750677/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174025897/400000000 : ℝ)*X 0 0+(2238717539/5000000000 : ℝ)*X 0 1+(2113685753/5000000000 : ℝ)*X 0 2+(174025897/400000000 : ℝ)*X 1 0+(2238717539/5000000000 : ℝ)*X 1 1+(2113685753/5000000000 : ℝ)*X 1 2+(174025897/400000000 : ℝ)*X 2 0+(2238717539/5000000000 : ℝ)*X 2 1+(2113685753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1243_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (537791716727934227067219579/65650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (788986317/50000000000000 : ℝ)*(base19) + (878761489/50000000000000 : ℝ)*(base23) + (81995427/50000000000000 : ℝ)*(lower2) + (101647451/50000000000000 : ℝ)*(upper3) + (48387671/20000000000000 : ℝ)*(upper5) + (6025877585583651/100000000000000 : ℝ)*(major0) + (6025877585583651/100000000000000 : ℝ)*(major1) + (6025877585583651/100000000000000 : ℝ)*(major2) + (8072859919326667/100000000000000 : ℝ)*(sp0) + (8072913633058411/100000000000000 : ℝ)*(sp1) + (2018228363377017/25000000000000 : ℝ)*(sp2) + (397881261537993/10000000000000 : ℝ)*(sp3) + (27645852189/50000000000000 : ℝ)*(sp4) + (3383962037/12500000000000 : ℝ)*(sp7) + (1989419843538113/50000000000000 : ℝ)*(f.failure) + (1614583042206209/20000000000000 : ℝ)*(f.sum) + (21546094502043/6565000000000000000000000000 : ℝ)*base65 + (1844824314056546807/262600000000000000000000000000000 : ℝ)*base68 + (685537269486346807/262600000000000000000000000000000 : ℝ)*base70 + (615128522482053193/262600000000000000000000000000000 : ℝ)*base71 + (3572499978389/820625000000000000000000000 : ℝ)*base74 + (1838846331672146807/262600000000000000000000000000000 : ℝ)*base76 + (1738137750870746807/262600000000000000000000000000000 : ℝ)*base78 + (4149049072354346807/262600000000000000000000000000000 : ℝ)*base80 + (6096959250883/6565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3993291/312500000000000000000 : ℝ)*base89 + (3993291/312500000000000000000 : ℝ)*base91 + (3993291/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35060792435822936253063/78906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (586806209/100000000000000 : ℝ)*(base19) + (104739817/10000000000000 : ℝ)*(base23) + (54346977/20000000000000 : ℝ)*(lower1) + (38993731/50000000000000 : ℝ)*(upper2) + (5656929/5000000000000 : ℝ)*(upper3) + (47315426665793/781250000000 : ℝ)*(major0) + (47315426665793/781250000000 : ℝ)*(major1) + (47315426665793/781250000000 : ℝ)*(major2) + (7050385801/100000000000000 : ℝ)*(sp2) + (65562021/10000000000000 : ℝ)*(sp3) + (4056886288252243/50000000000000 : ℝ)*(sp4) + (8113771989698277/100000000000000 : ℝ)*(sp5) + (1622752895744103/20000000000000 : ℝ)*(sp6) + (499871997438393/12500000000000 : ℝ)*(sp7) + (3998976635127353/100000000000000 : ℝ)*(f.failure) + (4056886288252243/50000000000000 : ℝ)*(f.sum) + (605331813073/252500000000000000000000000 : ℝ)*base66 + (1022719011518651/78906250000000000000000000000 : ℝ)*base68 + (564073580143651/78906250000000000000000000000 : ℝ)*base70 + (4145928449690229/315625000000000000000000000000 : ℝ)*base72 + (911211062781/505000000000000000000000000 : ℝ)*base74 + (845740601684177/157812500000000000000000000000 : ℝ)*base76 + (6122808144028521/315625000000000000000000000000 : ℝ)*base77 + (1059429028052927/157812500000000000000000000000 : ℝ)*base80 + (1783628527319/505000000000000000000000000 : ℝ)*base81 + (5712971/625000000000000000000 : ℝ)*base89 + (5712971/625000000000000000000 : ℝ)*base91 + (5712971/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1243_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1243_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1243_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1243_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1243_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1243_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8435/2048 : ℝ) ≤ p) (hpb : p ≤ (2109/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9465507/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1243_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
