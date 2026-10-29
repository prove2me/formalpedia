-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:42.14299+00:00
-- url     : https://prove2.me/submissions/7c40e589-d88d-4ba9-b4d5-5357300832e2

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
theorem support_rectangle_w1429_s6_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971129629/10000000000 : ℝ)*x 0 + (5408224637/10000000000 : ℝ)*x 1 + (262345067/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971129629/10000000000 : ℝ)^4389 ≤ (12025153382777/100000000000000 : ℝ)^3365 := by
    have hnat : (1971129629 : ℕ)^4389*100000000000000^3365 ≤ 12025153382777^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971129629 10000000000 12025153382777 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408224637/10000000000 : ℝ)^4389 ≤ (22428016090077/50000000000000 : ℝ)^3365 := by
    have hnat : (5408224637 : ℕ)^4389*50000000000000^3365 ≤ 22428016090077^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408224637 10000000000 22428016090077 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262345067/500000000 : ℝ)^4389 ≤ (43118814419557/100000000000000 : ℝ)^3365 := by
    have hnat : (262345067 : ℕ)^4389*100000000000000^3365 ≤ 43118814419557^3365*500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262345067 500000000 43118814419557 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971129629/10000000000 : ℝ), (5408224637/10000000000 : ℝ), (262345067/500000000 : ℝ)] ![(12025153382777/100000000000000 : ℝ), (22428016090077/50000000000000 : ℝ), (43118814419557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971129629/10000000000 : ℝ)|^4389 ≤ (12025153382777/100000000000000 : ℝ)^3365
        have hw : |(-1971129629/10000000000 : ℝ)|=(1971129629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408224637/10000000000 : ℝ)|^4389 ≤ (22428016090077/50000000000000 : ℝ)^3365
        have hw : |(5408224637/10000000000 : ℝ)|=(5408224637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262345067/500000000 : ℝ)|^4389 ≤ (43118814419557/100000000000000 : ℝ)^3365
        have hw : |(262345067/500000000 : ℝ)|=(262345067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673664319/5000000000 : ℝ)*x 0 + (-1026630993/5000000000 : ℝ)*x 1 + (81982833/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673664319/5000000000 : ℝ)^4389 ≤ (44198391365499/100000000000000 : ℝ)^3365 := by
    have hnat : (2673664319 : ℕ)^4389*100000000000000^3365 ≤ 44198391365499^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673664319 5000000000 44198391365499 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026630993/5000000000 : ℝ)^4389 ≤ (2536558899807/20000000000000 : ℝ)^3365 := by
    have hnat : (1026630993 : ℕ)^4389*20000000000000^3365 ≤ 2536558899807^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026630993 5000000000 2536558899807 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81982833/156250000 : ℝ)^4389 ≤ (5389851764929/12500000000000 : ℝ)^3365 := by
    have hnat : (81982833 : ℕ)^4389*12500000000000^3365 ≤ 5389851764929^3365*156250000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81982833 156250000 5389851764929 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673664319/5000000000 : ℝ), (-1026630993/5000000000 : ℝ), (81982833/156250000 : ℝ)] ![(44198391365499/100000000000000 : ℝ), (2536558899807/20000000000000 : ℝ), (5389851764929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673664319/5000000000 : ℝ)|^4389 ≤ (44198391365499/100000000000000 : ℝ)^3365
        have hw : |(2673664319/5000000000 : ℝ)|=(2673664319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026630993/5000000000 : ℝ)|^4389 ≤ (2536558899807/20000000000000 : ℝ)^3365
        have hw : |(-1026630993/5000000000 : ℝ)|=(1026630993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81982833/156250000 : ℝ)|^4389 ≤ (5389851764929/12500000000000 : ℝ)^3365
        have hw : |(81982833/156250000 : ℝ)|=(81982833/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673664317/5000000000 : ℝ)*x 0 + (40991417/78125000 : ℝ)*x 1 + (-1026630953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673664317/5000000000 : ℝ)^4389 ≤ (5524798915297/12500000000000 : ℝ)^3365 := by
    have hnat : (2673664317 : ℕ)^4389*12500000000000^3365 ≤ 5524798915297^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673664317 5000000000 5524798915297 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40991417/78125000 : ℝ)^4389 ≤ (5389851850679/12500000000000 : ℝ)^3365 := by
    have hnat : (40991417 : ℕ)^4389*12500000000000^3365 ≤ 5389851850679^3365*78125000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40991417 78125000 5389851850679 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026630953/5000000000 : ℝ)^4389 ≤ (3170698463627/25000000000000 : ℝ)^3365 := by
    have hnat : (1026630953 : ℕ)^4389*25000000000000^3365 ≤ 3170698463627^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026630953 5000000000 3170698463627 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673664317/5000000000 : ℝ), (40991417/78125000 : ℝ), (-1026630953/5000000000 : ℝ)] ![(5524798915297/12500000000000 : ℝ), (5389851850679/12500000000000 : ℝ), (3170698463627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673664317/5000000000 : ℝ)|^4389 ≤ (5524798915297/12500000000000 : ℝ)^3365
        have hw : |(2673664317/5000000000 : ℝ)|=(2673664317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40991417/78125000 : ℝ)|^4389 ≤ (5389851850679/12500000000000 : ℝ)^3365
        have hw : |(40991417/78125000 : ℝ)|=(40991417/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026630953/5000000000 : ℝ)|^4389 ≤ (3170698463627/25000000000000 : ℝ)^3365
        have hw : |(-1026630953/5000000000 : ℝ)|=(1026630953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33627913/78125000 : ℝ)*x 0 + (2066528189/5000000000 : ℝ)*x 1 + (1120513133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33627913/78125000 : ℝ)^4389 ≤ (33304686086183/100000000000000 : ℝ)^3365 := by
    have hnat : (33627913 : ℕ)^4389*100000000000000^3365 ≤ 33304686086183^3365*78125000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33627913 78125000 33304686086183 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066528189/5000000000 : ℝ)^4389 ≤ (31586333528739/100000000000000 : ℝ)^3365 := by
    have hnat : (2066528189 : ℕ)^4389*100000000000000^3365 ≤ 31586333528739^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066528189 5000000000 31586333528739 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120513133/2500000000 : ℝ)^4389 ≤ (8777245093511/25000000000000 : ℝ)^3365 := by
    have hnat : (1120513133 : ℕ)^4389*25000000000000^3365 ≤ 8777245093511^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120513133 2500000000 8777245093511 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33627913/78125000 : ℝ), (2066528189/5000000000 : ℝ), (1120513133/2500000000 : ℝ)] ![(33304686086183/100000000000000 : ℝ), (31586333528739/100000000000000 : ℝ), (8777245093511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33627913/78125000 : ℝ)|^4389 ≤ (33304686086183/100000000000000 : ℝ)^3365
        have hw : |(33627913/78125000 : ℝ)|=(33627913/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066528189/5000000000 : ℝ)|^4389 ≤ (31586333528739/100000000000000 : ℝ)^3365
        have hw : |(2066528189/5000000000 : ℝ)|=(2066528189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120513133/2500000000 : ℝ)|^4389 ≤ (8777245093511/25000000000000 : ℝ)^3365
        have hw : |(1120513133/2500000000 : ℝ)|=(1120513133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971140939/10000000000 : ℝ)*x 0 + (5247483229/10000000000 : ℝ)*x 1 + (1351909937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971140939/10000000000 : ℝ)^4389 ≤ (3006310844473/25000000000000 : ℝ)^3365 := by
    have hnat : (1971140939 : ℕ)^4389*25000000000000^3365 ≤ 3006310844473^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971140939 10000000000 3006310844473 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247483229/10000000000 : ℝ)^4389 ≤ (43125051651593/100000000000000 : ℝ)^3365 := by
    have hnat : (5247483229 : ℕ)^4389*100000000000000^3365 ≤ 43125051651593^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247483229 10000000000 43125051651593 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351909937/2500000000 : ℝ)^4389 ≤ (8969940991983/20000000000000 : ℝ)^3365 := by
    have hnat : (1351909937 : ℕ)^4389*20000000000000^3365 ≤ 8969940991983^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351909937 2500000000 8969940991983 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971140939/10000000000 : ℝ), (5247483229/10000000000 : ℝ), (1351909937/2500000000 : ℝ)] ![(3006310844473/25000000000000 : ℝ), (43125051651593/100000000000000 : ℝ), (8969940991983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971140939/10000000000 : ℝ)|^4389 ≤ (3006310844473/25000000000000 : ℝ)^3365
        have hw : |(-1971140939/10000000000 : ℝ)|=(1971140939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247483229/10000000000 : ℝ)|^4389 ≤ (43125051651593/100000000000000 : ℝ)^3365
        have hw : |(5247483229/10000000000 : ℝ)|=(5247483229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351909937/2500000000 : ℝ)|^4389 ≤ (8969940991983/20000000000000 : ℝ)^3365
        have hw : |(1351909937/2500000000 : ℝ)|=(1351909937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652694409/5000000000 : ℝ)*x 0 + (-1892523757/10000000000 : ℝ)*x 1 + (1081527933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652694409/5000000000 : ℝ)^4389 ≤ (21873394019677/50000000000000 : ℝ)^3365 := by
    have hnat : (2652694409 : ℕ)^4389*50000000000000^3365 ≤ 21873394019677^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652694409 5000000000 21873394019677 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1892523757/10000000000 : ℝ)^4389 ≤ (11403507876349/100000000000000 : ℝ)^3365 := by
    have hnat : (1892523757 : ℕ)^4389*100000000000000^3365 ≤ 11403507876349^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892523757 10000000000 11403507876349 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081527933/2000000000 : ℝ)^4389 ≤ (11212426015513/25000000000000 : ℝ)^3365 := by
    have hnat : (1081527933 : ℕ)^4389*25000000000000^3365 ≤ 11212426015513^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081527933 2000000000 11212426015513 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652694409/5000000000 : ℝ), (-1892523757/10000000000 : ℝ), (1081527933/2000000000 : ℝ)] ![(21873394019677/50000000000000 : ℝ), (11403507876349/100000000000000 : ℝ), (11212426015513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652694409/5000000000 : ℝ)|^4389 ≤ (21873394019677/50000000000000 : ℝ)^3365
        have hw : |(2652694409/5000000000 : ℝ)|=(2652694409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1892523757/10000000000 : ℝ)|^4389 ≤ (11403507876349/100000000000000 : ℝ)^3365
        have hw : |(-1892523757/10000000000 : ℝ)|=(1892523757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081527933/2000000000 : ℝ)|^4389 ≤ (11212426015513/25000000000000 : ℝ)^3365
        have hw : |(1081527933/2000000000 : ℝ)|=(1081527933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305389051/10000000000 : ℝ)*x 0 + (1081527931/2000000000 : ℝ)*x 1 + (-1892523453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305389051/10000000000 : ℝ)^4389 ≤ (43746790545263/100000000000000 : ℝ)^3365 := by
    have hnat : (5305389051 : ℕ)^4389*100000000000000^3365 ≤ 43746790545263^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305389051 10000000000 43746790545263 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081527931/2000000000 : ℝ)^4389 ≤ (358797631631/800000000000 : ℝ)^3365 := by
    have hnat : (1081527931 : ℕ)^4389*800000000000^3365 ≤ 358797631631^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081527931 2000000000 358797631631 800000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892523453/10000000000 : ℝ)^4389 ≤ (2850876371789/25000000000000 : ℝ)^3365 := by
    have hnat : (1892523453 : ℕ)^4389*25000000000000^3365 ≤ 2850876371789^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892523453 10000000000 2850876371789 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305389051/10000000000 : ℝ), (1081527931/2000000000 : ℝ), (-1892523453/10000000000 : ℝ)] ![(43746790545263/100000000000000 : ℝ), (358797631631/800000000000 : ℝ), (2850876371789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305389051/10000000000 : ℝ)|^4389 ≤ (43746790545263/100000000000000 : ℝ)^3365
        have hw : |(5305389051/10000000000 : ℝ)|=(5305389051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081527931/2000000000 : ℝ)|^4389 ≤ (358797631631/800000000000 : ℝ)^3365
        have hw : |(1081527931/2000000000 : ℝ)|=(1081527931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892523453/10000000000 : ℝ)|^4389 ≤ (2850876371789/25000000000000 : ℝ)^3365
        have hw : |(-1892523453/10000000000 : ℝ)|=(1892523453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s6_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4304397539/10000000000 : ℝ)*x 0 + (4480793797/10000000000 : ℝ)*x 1 + (2067160727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304397539/10000000000 : ℝ)^4389 ≤ (8326233776443/25000000000000 : ℝ)^3365 := by
    have hnat : (4304397539 : ℕ)^4389*25000000000000^3365 ≤ 8326233776443^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304397539 10000000000 8326233776443 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480793797/10000000000 : ℝ)^4389 ≤ (2193507529731/6250000000000 : ℝ)^3365 := by
    have hnat : (4480793797 : ℕ)^4389*6250000000000^3365 ≤ 2193507529731^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480793797 10000000000 2193507529731 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067160727/5000000000 : ℝ)^4389 ≤ (6319788880863/20000000000000 : ℝ)^3365 := by
    have hnat : (2067160727 : ℕ)^4389*20000000000000^3365 ≤ 6319788880863^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067160727 5000000000 6319788880863 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304397539/10000000000 : ℝ), (4480793797/10000000000 : ℝ), (2067160727/5000000000 : ℝ)] ![(8326233776443/25000000000000 : ℝ), (2193507529731/6250000000000 : ℝ), (6319788880863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304397539/10000000000 : ℝ)|^4389 ≤ (8326233776443/25000000000000 : ℝ)^3365
        have hw : |(4304397539/10000000000 : ℝ)|=(4304397539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480793797/10000000000 : ℝ)|^4389 ≤ (2193507529731/6250000000000 : ℝ)^3365
        have hw : |(4480793797/10000000000 : ℝ)|=(4480793797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2067160727/5000000000 : ℝ)|^4389 ≤ (6319788880863/20000000000000 : ℝ)^3365
        have hw : |(2067160727/5000000000 : ℝ)|=(2067160727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (567/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1417/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1417/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1417/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1417/12500 : ℝ) ^ (1097/256 : ℝ) ≤ (17335752617647/195312500000000000 : ℝ) := by
    have hpowers : (1417/12500 : ℝ)^1097 ≤ (17335752617647/195312500000000000 : ℝ)^256 := by
      have hnat : (1417 : ℕ)^1097*195312500000000000^256 ≤ 17335752617647^256*12500^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1417 12500 17335752617647 195312500000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1417/12500 : ℝ)) (X := (17335752617647/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (1097/256 : ℝ) ≤ (27512578369560601/100000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^1097 ≤ (27512578369560601/100000000000000000000 : ℝ)^256 := by
      have hnat : (14761 : ℕ)^1097*100000000000000000000^256 ≤ 27512578369560601^256*100000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 27512578369560601 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (27512578369560601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (97673585752617647/97656250000000000 : ℝ) ≤ (10000414234670407/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (97673585752617647/97656250000000000 : ℝ)^256 ≤ (10000414234670407/10000000000000000 : ℝ)^1097 := by
      have hnat : (97673585752617647 : ℕ)^256*10000000000000000^1097 ≤ 10000414234670407^1097*97656250000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97673585752617647 97656250000000000 10000414234670407 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000414234670407/10000000000000000 : ℝ)) (X := (97673585752617647/97656250000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007277696741959173/20000000000000000000 : ℝ) ≤ (5000424528384447/5000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (20007277696741959173/20000000000000000000 : ℝ)^256 ≤ (5000424528384447/5000000000000000 : ℝ)^1097 := by
      have hnat : (20007277696741959173 : ℕ)^256*5000000000000000^1097 ≤ 5000424528384447^1097*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007277696741959173 20000000000000000000 5000424528384447 5000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000424528384447/5000000000000000 : ℝ)) (X := (20007277696741959173/20000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027512578369560601/50000000000000000000 : ℝ) ≤ (10001283878867381/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50027512578369560601/50000000000000000000 : ℝ)^256 ≤ (10001283878867381/10000000000000000 : ℝ)^1097 := by
      have hnat : (50027512578369560601 : ℕ)^256*10000000000000000^1097 ≤ 10001283878867381^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027512578369560601 50000000000000000000 10001283878867381 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001283878867381/10000000000000000 : ℝ)) (X := (50027512578369560601/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17335752617647/195312500000000000 : ℝ) ≤ ((34241560467129246711/34250000000000000000 : ℝ)+2*(434822098487/342500000000000 : ℝ)*(1417/12500 : ℝ))^(1097/256 : ℝ) := by
    rw [show (34241560467129246711/34250000000000000000 : ℝ)+2*(434822098487/342500000000000 : ℝ)*(1417/12500 : ℝ)=(10000414234670407/10000000000000000 : ℝ) by norm_num, show 1+2*(17335752617647/195312500000000000 : ℝ)=(97673585752617647/97656250000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27512578369560601/100000000000000000000 : ℝ)+(17335752617647/195312500000000000 : ℝ) ≤ ((34241560467129246711/34250000000000000000 : ℝ)+(434822098487/342500000000000 : ℝ)*((14761/100000 : ℝ)+(1417/12500 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (34241560467129246711/34250000000000000000 : ℝ)+(434822098487/342500000000000 : ℝ)*((14761/100000 : ℝ)+(1417/12500 : ℝ))=(5000424528384447/5000000000000000 : ℝ) by norm_num, show 1+(27512578369560601/100000000000000000000 : ℝ)+(17335752617647/195312500000000000 : ℝ)=(20007277696741959173/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27512578369560601/100000000000000000000 : ℝ) ≤ ((34241560467129246711/34250000000000000000 : ℝ)+2*(434822098487/342500000000000 : ℝ)*(14761/100000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (34241560467129246711/34250000000000000000 : ℝ)+2*(434822098487/342500000000000 : ℝ)*(14761/100000 : ℝ)=(10001283878867381/10000000000000000 : ℝ) by norm_num, show 1+2*(27512578369560601/100000000000000000000 : ℝ)=(50027512578369560601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34241560467129246711/34250000000000000000 : ℝ)*(X 1 0+X 2 0)+(434822098487/342500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34241560467129246711/34250000000000000000 : ℝ)) (alpha := (434822098487/342500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34241560467129246711/34250000000000000000 : ℝ)*(X 0 1+X 2 1)+(434822098487/342500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34241560467129246711/34250000000000000000 : ℝ)) (alpha := (434822098487/342500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34241560467129246711/34250000000000000000 : ℝ)*(X 0 2+X 1 2)+(434822098487/342500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1417/12500 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34241560467129246711/34250000000000000000 : ℝ)) (alpha := (434822098487/342500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1971129629/10000000000 : ℝ)*X 0 0+(5408224637/10000000000 : ℝ)*X 0 1+(262345067/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673664319/5000000000 : ℝ)*X 1 0+(-1026630993/5000000000 : ℝ)*X 1 1+(81982833/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673664317/5000000000 : ℝ)*X 2 0+(40991417/78125000 : ℝ)*X 2 1+(-1026630953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33627913/78125000 : ℝ)*X 0 0+(2066528189/5000000000 : ℝ)*X 0 1+(1120513133/2500000000 : ℝ)*X 0 2+(33627913/78125000 : ℝ)*X 1 0+(2066528189/5000000000 : ℝ)*X 1 1+(1120513133/2500000000 : ℝ)*X 1 2+(33627913/78125000 : ℝ)*X 2 0+(2066528189/5000000000 : ℝ)*X 2 1+(1120513133/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1971140939/10000000000 : ℝ)*X 0 0+(5247483229/10000000000 : ℝ)*X 0 1+(1351909937/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652694409/5000000000 : ℝ)*X 1 0+(-1892523757/10000000000 : ℝ)*X 1 1+(1081527933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305389051/10000000000 : ℝ)*X 2 0+(1081527931/2000000000 : ℝ)*X 2 1+(-1892523453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304397539/10000000000 : ℝ)*X 0 0+(4480793797/10000000000 : ℝ)*X 0 1+(2067160727/5000000000 : ℝ)*X 0 2+(4304397539/10000000000 : ℝ)*X 1 0+(4480793797/10000000000 : ℝ)*X 1 1+(2067160727/5000000000 : ℝ)*X 1 2+(4304397539/10000000000 : ℝ)*X 2 0+(4480793797/10000000000 : ℝ)*X 2 1+(2067160727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4967031037362237682595789067/856250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253736011/25000000000000 : ℝ)*(base19) + (946098129/100000000000000 : ℝ)*(base23) + (17167331/50000000000000 : ℝ)*(lower2) + (41540131/50000000000000 : ℝ)*(upper3) + (34348223/25000000000000 : ℝ)*(upper5) + (2266039569724133/50000000000000 : ℝ)*(major0) + (2266039569724133/50000000000000 : ℝ)*(major1) + (2266039569724133/50000000000000 : ℝ)*(major2) + (6198753378421591/100000000000000 : ℝ)*(sp0) + (3099388063655697/50000000000000 : ℝ)*(sp1) + (6198776196157309/100000000000000 : ℝ)*(sp2) + (1432685625721277/50000000000000 : ℝ)*(sp3) + (2970479231/12500000000000 : ℝ)*(sp4) + (9691834791/100000000000000 : ℝ)*(sp7) + (1432690471638673/50000000000000 : ℝ)*(f.failure) + (3099388571127719/50000000000000 : ℝ)*(f.sum) + (8787573150323/4281250000000000000000000000 : ℝ)*base65 + (11057657136280323437/1712500000000000000000000000000000 : ℝ)*base68 + (31229197355730323437/1712500000000000000000000000000000 : ℝ)*base70 + (5456004354067823437/1712500000000000000000000000000000 : ℝ)*base72 + (26935064294167/17125000000000000000000000000 : ℝ)*base73 + (27796879302080323437/1712500000000000000000000000000000 : ℝ)*base76 + (19334420368542823437/1712500000000000000000000000000000 : ℝ)*base78 + (376939385342823437/1712500000000000000000000000000000 : ℝ)*base80 + (36391473229229/8562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (48478579/5000000000000000000000 : ℝ)*base89 + (48478579/5000000000000000000000 : ℝ)*base91 + (48478579/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (283502009028716031731158917/53515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (365363133/50000000000000 : ℝ)*(base19) + (264834753/20000000000000 : ℝ)*(base23) + (137384099/100000000000000 : ℝ)*(lower1) + (9147969/6250000000000 : ℝ)*(upper3) + (90946411/100000000000000 : ℝ)*(lower4) + (23983457/25000000000000 : ℝ)*(upper5) + (142658020875901/3125000000000 : ℝ)*(major0) + (142658020875901/3125000000000 : ℝ)*(major1) + (142658020875901/3125000000000 : ℝ)*(major2) + (74791529/400000000000 : ℝ)*(sp2) + (3121941181806147/50000000000000 : ℝ)*(sp4) + (1560970408221507/25000000000000 : ℝ)*(sp5) + (3121931170778139/50000000000000 : ℝ)*(sp6) + (1443115397930079/50000000000000 : ℝ)*(sp7) + (1443115397930079/50000000000000 : ℝ)*(f.failure) + (3121941181806147/50000000000000 : ℝ)*(f.sum) + (12148603507273/2140625000000000000000000000 : ℝ)*base65 + (2421491851281013389/107031250000000000000000000000000 : ℝ)*base68 + (331005717700236611/107031250000000000000000000000000 : ℝ)*base69 + (5614978580345549111/107031250000000000000000000000000 : ℝ)*base71 + (49226107037967/8562500000000000000000000000 : ℝ)*base73 + (5399579987765388389/107031250000000000000000000000000 : ℝ)*base76 + (673642910784611611/107031250000000000000000000000000 : ℝ)*base77 + (1162474946634611611/107031250000000000000000000000000 : ℝ)*base79 + (14031935325533/8562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (21438883/5000000000000000000000 : ℝ)*base90 + (21438883/5000000000000000000000 : ℝ)*base92 + (21438883/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1429_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1429_box_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905232127/5000000000 : ℝ)*x 0 + (1077251793/2000000000 : ℝ)*x 1 + (5386259457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905232127/5000000000 : ℝ)^4389 ≤ (1076288525763/10000000000000 : ℝ)^3365 := by
    have hnat : (905232127 : ℕ)^4389*10000000000000^3365 ≤ 1076288525763^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905232127 5000000000 1076288525763 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077251793/2000000000 : ℝ)^4389 ≤ (44618554708127/100000000000000 : ℝ)^3365 := by
    have hnat : (1077251793 : ℕ)^4389*100000000000000^3365 ≤ 44618554708127^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077251793 2000000000 44618554708127 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386259457/10000000000 : ℝ)^4389 ≤ (5577320002999/12500000000000 : ℝ)^3365 := by
    have hnat : (5386259457 : ℕ)^4389*12500000000000^3365 ≤ 5577320002999^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386259457 10000000000 5577320002999 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905232127/5000000000 : ℝ), (1077251793/2000000000 : ℝ), (5386259457/10000000000 : ℝ)] ![(1076288525763/10000000000000 : ℝ), (44618554708127/100000000000000 : ℝ), (5577320002999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905232127/5000000000 : ℝ)|^4389 ≤ (1076288525763/10000000000000 : ℝ)^3365
        have hw : |(-905232127/5000000000 : ℝ)|=(905232127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077251793/2000000000 : ℝ)|^4389 ≤ (44618554708127/100000000000000 : ℝ)^3365
        have hw : |(1077251793/2000000000 : ℝ)|=(1077251793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386259457/10000000000 : ℝ)|^4389 ≤ (5577320002999/12500000000000 : ℝ)^3365
        have hw : |(5386259457/10000000000 : ℝ)|=(5386259457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286062639/10000000000 : ℝ)*x 0 + (-1948120411/10000000000 : ℝ)*x 1 + (538625917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286062639/10000000000 : ℝ)^4389 ≤ (8707810147983/20000000000000 : ℝ)^3365 := by
    have hnat : (5286062639 : ℕ)^4389*20000000000000^3365 ≤ 8707810147983^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286062639 10000000000 8707810147983 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948120411/10000000000 : ℝ)^4389 ≤ (11842392324653/100000000000000 : ℝ)^3365 := by
    have hnat : (1948120411 : ℕ)^4389*100000000000000^3365 ≤ 11842392324653^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948120411 10000000000 11842392324653 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538625917/1000000000 : ℝ)^4389 ≤ (44618556923071/100000000000000 : ℝ)^3365 := by
    have hnat : (538625917 : ℕ)^4389*100000000000000^3365 ≤ 44618556923071^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538625917 1000000000 44618556923071 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286062639/10000000000 : ℝ), (-1948120411/10000000000 : ℝ), (538625917/1000000000 : ℝ)] ![(8707810147983/20000000000000 : ℝ), (11842392324653/100000000000000 : ℝ), (44618556923071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286062639/10000000000 : ℝ)|^4389 ≤ (8707810147983/20000000000000 : ℝ)^3365
        have hw : |(5286062639/10000000000 : ℝ)|=(5286062639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948120411/10000000000 : ℝ)|^4389 ≤ (11842392324653/100000000000000 : ℝ)^3365
        have hw : |(-1948120411/10000000000 : ℝ)|=(1948120411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538625917/1000000000 : ℝ)|^4389 ≤ (44618556923071/100000000000000 : ℝ)^3365
        have hw : |(538625917/1000000000 : ℝ)|=(538625917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286062841/10000000000 : ℝ)*x 0 + (5386259093/10000000000 : ℝ)*x 1 + (-1948120243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286062841/10000000000 : ℝ)^4389 ≤ (43539052910009/100000000000000 : ℝ)^3365 := by
    have hnat : (5286062841 : ℕ)^4389*100000000000000^3365 ≤ 43539052910009^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286062841 10000000000 43539052910009 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386259093/10000000000 : ℝ)^4389 ≤ (11154639022779/25000000000000 : ℝ)^3365 := by
    have hnat : (5386259093 : ℕ)^4389*25000000000000^3365 ≤ 11154639022779^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386259093 10000000000 11154639022779 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948120243/10000000000 : ℝ)^4389 ≤ (740149437039/6250000000000 : ℝ)^3365 := by
    have hnat : (1948120243 : ℕ)^4389*6250000000000^3365 ≤ 740149437039^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948120243 10000000000 740149437039 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286062841/10000000000 : ℝ), (5386259093/10000000000 : ℝ), (-1948120243/10000000000 : ℝ)] ![(43539052910009/100000000000000 : ℝ), (11154639022779/25000000000000 : ℝ), (740149437039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286062841/10000000000 : ℝ)|^4389 ≤ (43539052910009/100000000000000 : ℝ)^3365
        have hw : |(5286062841/10000000000 : ℝ)|=(5286062841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386259093/10000000000 : ℝ)|^4389 ≤ (11154639022779/25000000000000 : ℝ)^3365
        have hw : |(5386259093/10000000000 : ℝ)|=(5386259093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948120243/10000000000 : ℝ)|^4389 ≤ (740149437039/6250000000000 : ℝ)^3365
        have hw : |(-1948120243/10000000000 : ℝ)|=(1948120243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4450678527/10000000000 : ℝ)*x 0 + (2117465767/5000000000 : ℝ)*x 1 + (4234931413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4450678527/10000000000 : ℝ)^4389 ≤ (34788775311369/100000000000000 : ℝ)^3365 := by
    have hnat : (4450678527 : ℕ)^4389*100000000000000^3365 ≤ 34788775311369^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450678527 10000000000 34788775311369 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117465767/5000000000 : ℝ)^4389 ≤ (32605612944951/100000000000000 : ℝ)^3365 := by
    have hnat : (2117465767 : ℕ)^4389*100000000000000^3365 ≤ 32605612944951^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117465767 5000000000 32605612944951 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234931413/10000000000 : ℝ)^4389 ≤ (32605611729851/100000000000000 : ℝ)^3365 := by
    have hnat : (4234931413 : ℕ)^4389*100000000000000^3365 ≤ 32605611729851^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234931413 10000000000 32605611729851 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4450678527/10000000000 : ℝ), (2117465767/5000000000 : ℝ), (4234931413/10000000000 : ℝ)] ![(34788775311369/100000000000000 : ℝ), (32605612944951/100000000000000 : ℝ), (32605611729851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4450678527/10000000000 : ℝ)|^4389 ≤ (34788775311369/100000000000000 : ℝ)^3365
        have hw : |(4450678527/10000000000 : ℝ)|=(4450678527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117465767/5000000000 : ℝ)|^4389 ≤ (32605612944951/100000000000000 : ℝ)^3365
        have hw : |(2117465767/5000000000 : ℝ)|=(2117465767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234931413/10000000000 : ℝ)|^4389 ≤ (32605611729851/100000000000000 : ℝ)^3365
        have hw : |(4234931413/10000000000 : ℝ)|=(4234931413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213453483/1000000000 : ℝ)*x 0 + (5266523291/10000000000 : ℝ)*x 1 + (2633261739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213453483/1000000000 : ℝ)^4389 ≤ (1334148414087/10000000000000 : ℝ)^3365 := by
    have hnat : (213453483 : ℕ)^4389*10000000000000^3365 ≤ 1334148414087^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213453483 1000000000 1334148414087 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266523291/10000000000 : ℝ)^4389 ≤ (2708078557351/6250000000000 : ℝ)^3365 := by
    have hnat : (5266523291 : ℕ)^4389*6250000000000^3365 ≤ 2708078557351^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266523291 10000000000 2708078557351 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633261739/5000000000 : ℝ)^4389 ≤ (21664629462151/50000000000000 : ℝ)^3365 := by
    have hnat : (2633261739 : ℕ)^4389*50000000000000^3365 ≤ 21664629462151^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633261739 5000000000 21664629462151 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213453483/1000000000 : ℝ), (5266523291/10000000000 : ℝ), (2633261739/5000000000 : ℝ)] ![(1334148414087/10000000000000 : ℝ), (2708078557351/6250000000000 : ℝ), (21664629462151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213453483/1000000000 : ℝ)|^4389 ≤ (1334148414087/10000000000000 : ℝ)^3365
        have hw : |(-213453483/1000000000 : ℝ)|=(213453483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266523291/10000000000 : ℝ)|^4389 ≤ (2708078557351/6250000000000 : ℝ)^3365
        have hw : |(5266523291/10000000000 : ℝ)|=(5266523291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633261739/5000000000 : ℝ)|^4389 ≤ (21664629462151/50000000000000 : ℝ)^3365
        have hw : |(2633261739/5000000000 : ℝ)|=(2633261739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684930111/5000000000 : ℝ)*x 0 + (-199673407/1000000000 : ℝ)*x 1 + (1316630721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684930111/5000000000 : ℝ)^4389 ≤ (44441454950031/100000000000000 : ℝ)^3365 := by
    have hnat : (2684930111 : ℕ)^4389*100000000000000^3365 ≤ 44441454950031^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684930111 5000000000 44441454950031 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199673407/1000000000 : ℝ)^4389 ≤ (12229292482721/100000000000000 : ℝ)^3365 := by
    have hnat : (199673407 : ℕ)^4389*100000000000000^3365 ≤ 12229292482721^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199673407 1000000000 12229292482721 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316630721/2500000000 : ℝ)^4389 ≤ (10832313137531/25000000000000 : ℝ)^3365 := by
    have hnat : (1316630721 : ℕ)^4389*25000000000000^3365 ≤ 10832313137531^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316630721 2500000000 10832313137531 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684930111/5000000000 : ℝ), (-199673407/1000000000 : ℝ), (1316630721/2500000000 : ℝ)] ![(44441454950031/100000000000000 : ℝ), (12229292482721/100000000000000 : ℝ), (10832313137531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684930111/5000000000 : ℝ)|^4389 ≤ (44441454950031/100000000000000 : ℝ)^3365
        have hw : |(2684930111/5000000000 : ℝ)|=(2684930111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199673407/1000000000 : ℝ)|^4389 ≤ (12229292482721/100000000000000 : ℝ)^3365
        have hw : |(-199673407/1000000000 : ℝ)|=(199673407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316630721/2500000000 : ℝ)|^4389 ≤ (10832313137531/25000000000000 : ℝ)^3365
        have hw : |(1316630721/2500000000 : ℝ)|=(1316630721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684929779/5000000000 : ℝ)*x 0 + (5266524103/10000000000 : ℝ)*x 1 + (-199673333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684929779/5000000000 : ℝ)^4389 ≤ (4444144778243/10000000000000 : ℝ)^3365 := by
    have hnat : (2684929779 : ℕ)^4389*10000000000000^3365 ≤ 4444144778243^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684929779 5000000000 4444144778243 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266524103/10000000000 : ℝ)^4389 ≤ (43329265631139/100000000000000 : ℝ)^3365 := by
    have hnat : (5266524103 : ℕ)^4389*100000000000000^3365 ≤ 43329265631139^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266524103 10000000000 43329265631139 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199673333/1000000000 : ℝ)^4389 ≤ (152866082141/1250000000000 : ℝ)^3365 := by
    have hnat : (199673333 : ℕ)^4389*1250000000000^3365 ≤ 152866082141^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199673333 1000000000 152866082141 1250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684929779/5000000000 : ℝ), (5266524103/10000000000 : ℝ), (-199673333/1000000000 : ℝ)] ![(4444144778243/10000000000000 : ℝ), (43329265631139/100000000000000 : ℝ), (152866082141/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684929779/5000000000 : ℝ)|^4389 ≤ (4444144778243/10000000000000 : ℝ)^3365
        have hw : |(2684929779/5000000000 : ℝ)|=(2684929779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266524103/10000000000 : ℝ)|^4389 ≤ (43329265631139/100000000000000 : ℝ)^3365
        have hw : |(5266524103/10000000000 : ℝ)|=(5266524103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199673333/1000000000 : ℝ)|^4389 ≤ (152866082141/1250000000000 : ℝ)^3365
        have hw : |(-199673333/1000000000 : ℝ)|=(199673333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415702189/1000000000 : ℝ)*x 0 + (1095427147/2500000000 : ℝ)*x 1 + (4381709193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415702189/1000000000 : ℝ)^4389 ≤ (15912716218451/50000000000000 : ℝ)^3365 := by
    have hnat : (415702189 : ℕ)^4389*50000000000000^3365 ≤ 15912716218451^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415702189 1000000000 15912716218451 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095427147/2500000000 : ℝ)^4389 ≤ (8521820174993/25000000000000 : ℝ)^3365 := by
    have hnat : (1095427147 : ℕ)^4389*25000000000000^3365 ≤ 8521820174993^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095427147 2500000000 8521820174993 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381709193/10000000000 : ℝ)^4389 ≤ (3408728683879/10000000000000 : ℝ)^3365 := by
    have hnat : (4381709193 : ℕ)^4389*10000000000000^3365 ≤ 3408728683879^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381709193 10000000000 3408728683879 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415702189/1000000000 : ℝ), (1095427147/2500000000 : ℝ), (4381709193/10000000000 : ℝ)] ![(15912716218451/50000000000000 : ℝ), (8521820174993/25000000000000 : ℝ), (3408728683879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415702189/1000000000 : ℝ)|^4389 ≤ (15912716218451/50000000000000 : ℝ)^3365
        have hw : |(415702189/1000000000 : ℝ)|=(415702189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095427147/2500000000 : ℝ)|^4389 ≤ (8521820174993/25000000000000 : ℝ)^3365
        have hw : |(1095427147/2500000000 : ℝ)|=(1095427147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381709193/10000000000 : ℝ)|^4389 ≤ (3408728683879/10000000000000 : ℝ)^3365
        have hw : |(4381709193/10000000000 : ℝ)|=(4381709193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_8 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066276061/10000000000 : ℝ)*x 0 + (2591851311/5000000000 : ℝ)*x 1 + (5400233891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066276061/10000000000 : ℝ)^4389 ≤ (12787744493869/100000000000000 : ℝ)^3365 := by
    have hnat : (2066276061 : ℕ)^4389*100000000000000^3365 ≤ 12787744493869^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066276061 10000000000 12787744493869 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591851311/5000000000 : ℝ)^4389 ≤ (42442647693309/100000000000000 : ℝ)^3365 := by
    have hnat : (2591851311 : ℕ)^4389*100000000000000^3365 ≤ 42442647693309^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591851311 5000000000 42442647693309 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400233891/10000000000 : ℝ)^4389 ≤ (2798100487267/6250000000000 : ℝ)^3365 := by
    have hnat : (5400233891 : ℕ)^4389*6250000000000^3365 ≤ 2798100487267^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400233891 10000000000 2798100487267 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066276061/10000000000 : ℝ), (2591851311/5000000000 : ℝ), (5400233891/10000000000 : ℝ)] ![(12787744493869/100000000000000 : ℝ), (42442647693309/100000000000000 : ℝ), (2798100487267/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066276061/10000000000 : ℝ)|^4389 ≤ (12787744493869/100000000000000 : ℝ)^3365
        have hw : |(-2066276061/10000000000 : ℝ)|=(2066276061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591851311/5000000000 : ℝ)|^4389 ≤ (42442647693309/100000000000000 : ℝ)^3365
        have hw : |(2591851311/5000000000 : ℝ)|=(2591851311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400233891/10000000000 : ℝ)|^4389 ≤ (2798100487267/6250000000000 : ℝ)^3365
        have hw : |(5400233891/10000000000 : ℝ)|=(5400233891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_9 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276278557/10000000000 : ℝ)*x 0 + (-1942320271/10000000000 : ℝ)*x 1 + (1350058409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276278557/10000000000 : ℝ)^4389 ≤ (43433969577409/100000000000000 : ℝ)^3365 := by
    have hnat : (5276278557 : ℕ)^4389*100000000000000^3365 ≤ 43433969577409^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276278557 10000000000 43433969577409 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942320271/10000000000 : ℝ)^4389 ≤ (11796425371681/100000000000000 : ℝ)^3365 := by
    have hnat : (1942320271 : ℕ)^4389*100000000000000^3365 ≤ 11796425371681^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942320271 10000000000 11796425371681 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350058409/2500000000 : ℝ)^4389 ≤ (22384802519463/50000000000000 : ℝ)^3365 := by
    have hnat : (1350058409 : ℕ)^4389*50000000000000^3365 ≤ 22384802519463^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350058409 2500000000 22384802519463 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276278557/10000000000 : ℝ), (-1942320271/10000000000 : ℝ), (1350058409/2500000000 : ℝ)] ![(43433969577409/100000000000000 : ℝ), (11796425371681/100000000000000 : ℝ), (22384802519463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276278557/10000000000 : ℝ)|^4389 ≤ (43433969577409/100000000000000 : ℝ)^3365
        have hw : |(5276278557/10000000000 : ℝ)|=(5276278557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942320271/10000000000 : ℝ)|^4389 ≤ (11796425371681/100000000000000 : ℝ)^3365
        have hw : |(-1942320271/10000000000 : ℝ)|=(1942320271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350058409/2500000000 : ℝ)|^4389 ≤ (22384802519463/50000000000000 : ℝ)^3365
        have hw : |(1350058409/2500000000 : ℝ)|=(1350058409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_10 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276278421/10000000000 : ℝ)*x 0 + (4320187/8000000 : ℝ)*x 1 + (-19423203/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276278421/10000000000 : ℝ)^4389 ≤ (43433968117179/100000000000000 : ℝ)^3365 := by
    have hnat : (5276278421 : ℕ)^4389*100000000000000^3365 ≤ 43433968117179^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276278421 10000000000 43433968117179 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4320187/8000000 : ℝ)^4389 ≤ (22384803135811/50000000000000 : ℝ)^3365 := by
    have hnat : (4320187 : ℕ)^4389*50000000000000^3365 ≤ 22384803135811^3365*8000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320187 8000000 22384803135811 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19423203/100000000 : ℝ)^4389 ≤ (5898212800703/50000000000000 : ℝ)^3365 := by
    have hnat : (19423203 : ℕ)^4389*50000000000000^3365 ≤ 5898212800703^3365*100000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19423203 100000000 5898212800703 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276278421/10000000000 : ℝ), (4320187/8000000 : ℝ), (-19423203/100000000 : ℝ)] ![(43433968117179/100000000000000 : ℝ), (22384803135811/50000000000000 : ℝ), (5898212800703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276278421/10000000000 : ℝ)|^4389 ≤ (43433968117179/100000000000000 : ℝ)^3365
        have hw : |(5276278421/10000000000 : ℝ)|=(5276278421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4320187/8000000 : ℝ)|^4389 ≤ (22384803135811/50000000000000 : ℝ)^3365
        have hw : |(4320187/8000000 : ℝ)|=(4320187/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19423203/100000000 : ℝ)|^4389 ≤ (5898212800703/50000000000000 : ℝ)^3365
        have hw : |(-19423203/100000000 : ℝ)|=(19423203/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_11 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4484395321/10000000000 : ℝ)*x 0 + (4217785683/10000000000 : ℝ)*x 1 + (843557247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4484395321/10000000000 : ℝ)^4389 ≤ (35132918464173/100000000000000 : ℝ)^3365 := by
    have hnat : (4484395321 : ℕ)^4389*100000000000000^3365 ≤ 35132918464173^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484395321 10000000000 35132918464173 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217785683/10000000000 : ℝ)^4389 ≤ (16216768995313/50000000000000 : ℝ)^3365 := by
    have hnat : (4217785683 : ℕ)^4389*50000000000000^3365 ≤ 16216768995313^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217785683 10000000000 16216768995313 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843557247/2000000000 : ℝ)^4389 ≤ (32433543527051/100000000000000 : ℝ)^3365 := by
    have hnat : (843557247 : ℕ)^4389*100000000000000^3365 ≤ 32433543527051^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843557247 2000000000 32433543527051 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4484395321/10000000000 : ℝ), (4217785683/10000000000 : ℝ), (843557247/2000000000 : ℝ)] ![(35132918464173/100000000000000 : ℝ), (16216768995313/50000000000000 : ℝ), (32433543527051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4484395321/10000000000 : ℝ)|^4389 ≤ (35132918464173/100000000000000 : ℝ)^3365
        have hw : |(4484395321/10000000000 : ℝ)|=(4484395321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217785683/10000000000 : ℝ)|^4389 ≤ (16216768995313/50000000000000 : ℝ)^3365
        have hw : |(4217785683/10000000000 : ℝ)|=(4217785683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(843557247/2000000000 : ℝ)|^4389 ≤ (32433543527051/100000000000000 : ℝ)^3365
        have hw : |(843557247/2000000000 : ℝ)|=(843557247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_12 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29357869/156250000 : ℝ)*x 0 + (5467055779/10000000000 : ℝ)*x 1 + (5255397041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29357869/156250000 : ℝ)^4389 ≤ (353018189021/3125000000000 : ℝ)^3365 := by
    have hnat : (29357869 : ℕ)^4389*3125000000000^3365 ≤ 353018189021^3365*156250000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29357869 156250000 353018189021 3125000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467055779/10000000000 : ℝ)^4389 ≤ (4549351773737/10000000000000 : ℝ)^3365 := by
    have hnat : (5467055779 : ℕ)^4389*10000000000000^3365 ≤ 4549351773737^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467055779 10000000000 4549351773737 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255397041/10000000000 : ℝ)^4389 ≤ (5401237525081/12500000000000 : ℝ)^3365 := by
    have hnat : (5255397041 : ℕ)^4389*12500000000000^3365 ≤ 5401237525081^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255397041 10000000000 5401237525081 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29357869/156250000 : ℝ), (5467055779/10000000000 : ℝ), (5255397041/10000000000 : ℝ)] ![(353018189021/3125000000000 : ℝ), (4549351773737/10000000000000 : ℝ), (5401237525081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29357869/156250000 : ℝ)|^4389 ≤ (353018189021/3125000000000 : ℝ)^3365
        have hw : |(-29357869/156250000 : ℝ)|=(29357869/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467055779/10000000000 : ℝ)|^4389 ≤ (4549351773737/10000000000000 : ℝ)^3365
        have hw : |(5467055779/10000000000 : ℝ)|=(5467055779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255397041/10000000000 : ℝ)|^4389 ≤ (5401237525081/12500000000000 : ℝ)^3365
        have hw : |(5255397041/10000000000 : ℝ)|=(5255397041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_13 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075528989/2000000000 : ℝ)*x 0 + (-2001152309/10000000000 : ℝ)*x 1 + (5255396511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075528989/2000000000 : ℝ)^4389 ≤ (695711036011/1562500000000 : ℝ)^3365 := by
    have hnat : (1075528989 : ℕ)^4389*1562500000000^3365 ≤ 695711036011^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075528989 2000000000 695711036011 1562500000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001152309/10000000000 : ℝ)^4389 ≤ (6132299583677/50000000000000 : ℝ)^3365 := by
    have hnat : (2001152309 : ℕ)^4389*50000000000000^3365 ≤ 6132299583677^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001152309 10000000000 6132299583677 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255396511/10000000000 : ℝ)^4389 ≤ (4320989451691/10000000000000 : ℝ)^3365 := by
    have hnat : (5255396511 : ℕ)^4389*10000000000000^3365 ≤ 4320989451691^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255396511 10000000000 4320989451691 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075528989/2000000000 : ℝ), (-2001152309/10000000000 : ℝ), (5255396511/10000000000 : ℝ)] ![(695711036011/1562500000000 : ℝ), (6132299583677/50000000000000 : ℝ), (4320989451691/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075528989/2000000000 : ℝ)|^4389 ≤ (695711036011/1562500000000 : ℝ)^3365
        have hw : |(1075528989/2000000000 : ℝ)|=(1075528989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001152309/10000000000 : ℝ)|^4389 ≤ (6132299583677/50000000000000 : ℝ)^3365
        have hw : |(-2001152309/10000000000 : ℝ)|=(2001152309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255396511/10000000000 : ℝ)|^4389 ≤ (4320989451691/10000000000000 : ℝ)^3365
        have hw : |(5255396511/10000000000 : ℝ)|=(5255396511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_14 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377645877/10000000000 : ℝ)*x 0 + (1313849147/2500000000 : ℝ)*x 1 + (-1000575473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377645877/10000000000 : ℝ)^4389 ≤ (4452551636969/10000000000000 : ℝ)^3365 := by
    have hnat : (5377645877 : ℕ)^4389*10000000000000^3365 ≤ 4452551636969^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377645877 10000000000 4452551636969 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313849147/2500000000 : ℝ)^4389 ≤ (2160494767133/5000000000000 : ℝ)^3365 := by
    have hnat : (1313849147 : ℕ)^4389*5000000000000^3365 ≤ 2160494767133^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313849147 2500000000 2160494767133 5000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000575473/5000000000 : ℝ)^4389 ≤ (6132294135897/50000000000000 : ℝ)^3365 := by
    have hnat : (1000575473 : ℕ)^4389*50000000000000^3365 ≤ 6132294135897^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000575473 5000000000 6132294135897 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377645877/10000000000 : ℝ), (1313849147/2500000000 : ℝ), (-1000575473/5000000000 : ℝ)] ![(4452551636969/10000000000000 : ℝ), (2160494767133/5000000000000 : ℝ), (6132294135897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377645877/10000000000 : ℝ)|^4389 ≤ (4452551636969/10000000000000 : ℝ)^3365
        have hw : |(5377645877/10000000000 : ℝ)|=(5377645877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313849147/2500000000 : ℝ)|^4389 ≤ (2160494767133/5000000000000 : ℝ)^3365
        have hw : |(1313849147/2500000000 : ℝ)|=(1313849147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000575473/5000000000 : ℝ)|^4389 ≤ (6132294135897/50000000000000 : ℝ)^3365
        have hw : |(-1000575473/5000000000 : ℝ)|=(1000575473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_box_15 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258080261/625000000 : ℝ)*x 0 + (879067403/2000000000 : ℝ)*x 1 + (4395337051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258080261/625000000 : ℝ)^4389 ≤ (1971796088121/6250000000000 : ℝ)^3365 := by
    have hnat : (258080261 : ℕ)^4389*6250000000000^3365 ≤ 1971796088121^3365*625000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258080261 625000000 1971796088121 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879067403/2000000000 : ℝ)^4389 ≤ (34225631107353/100000000000000 : ℝ)^3365 := by
    have hnat : (879067403 : ℕ)^4389*100000000000000^3365 ≤ 34225631107353^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879067403 2000000000 34225631107353 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4395337051/10000000000 : ℝ)^4389 ≤ (34225631472983/100000000000000 : ℝ)^3365 := by
    have hnat : (4395337051 : ℕ)^4389*100000000000000^3365 ≤ 34225631472983^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395337051 10000000000 34225631472983 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258080261/625000000 : ℝ), (879067403/2000000000 : ℝ), (4395337051/10000000000 : ℝ)] ![(1971796088121/6250000000000 : ℝ), (34225631107353/100000000000000 : ℝ), (34225631472983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258080261/625000000 : ℝ)|^4389 ≤ (1971796088121/6250000000000 : ℝ)^3365
        have hw : |(258080261/625000000 : ℝ)|=(258080261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879067403/2000000000 : ℝ)|^4389 ≤ (34225631107353/100000000000000 : ℝ)^3365
        have hw : |(879067403/2000000000 : ℝ)|=(879067403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4395337051/10000000000 : ℝ)|^4389 ≤ (34225631472983/100000000000000 : ℝ)^3365
        have hw : |(4395337051/10000000000 : ℝ)|=(4395337051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(629/1000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59113/100000 : ℝ) ∧ (2514/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16937/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (567/5000 : ℝ) ^ (1097/256 : ℝ) ≤ (8889333954185849/100000000000000000000 : ℝ) := by
    have hpowers : (567/5000 : ℝ)^1097 ≤ (8889333954185849/100000000000000000000 : ℝ)^256 := by
      have hnat : (567 : ℕ)^1097*100000000000000000000^256 ≤ 8889333954185849^256*5000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        567 5000 8889333954185849 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (567/5000 : ℝ)) (X := (8889333954185849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (1097/256 : ℝ) ≤ (1717540293631691/6250000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^1097 ≤ (1717540293631691/6250000000000000000 : ℝ)^256 := by
      have hnat : (14757 : ℕ)^1097*6250000000000000000^256 ≤ 1717540293631691^256*100000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 1717540293631691 6250000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (1717540293631691/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008889333954185849/50000000000000000000 : ℝ) ≤ (250010371533383/250000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50008889333954185849/50000000000000000000 : ℝ)^256 ≤ (250010371533383/250000000000000 : ℝ)^1097 := by
      have hnat : (50008889333954185849 : ℕ)^256*250000000000000^1097 ≤ 250010371533383^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008889333954185849 50000000000000000000 250010371533383 250000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250010371533383/250000000000000 : ℝ)) (X := (50008889333954185849/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007273995730458581/20000000000000000000 : ℝ) ≤ (1000084862504839/1000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (20007273995730458581/20000000000000000000 : ℝ)^256 ≤ (1000084862504839/1000000000000000 : ℝ)^1097 := by
      have hnat : (20007273995730458581 : ℕ)^256*1000000000000000^1097 ≤ 1000084862504839^1097*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007273995730458581 20000000000000000000 1000084862504839 1000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000084862504839/1000000000000000 : ℝ)) (X := (20007273995730458581/20000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126717540293631691/3125000000000000000 : ℝ) ≤ (500064119438073/500000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (3126717540293631691/3125000000000000000 : ℝ)^256 ≤ (500064119438073/500000000000000 : ℝ)^1097 := by
      have hnat : (3126717540293631691 : ℕ)^256*500000000000000^1097 ≤ 500064119438073^1097*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126717540293631691 3125000000000000000 500064119438073 500000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500064119438073/500000000000000 : ℝ)) (X := (3126717540293631691/3125000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8889333954185849/100000000000000000000 : ℝ) ≤ ((284679831834753007/284750000000000000 : ℝ)+2*(43376371307/34170000000000 : ℝ)*(567/5000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (284679831834753007/284750000000000000 : ℝ)+2*(43376371307/34170000000000 : ℝ)*(567/5000 : ℝ)=(250010371533383/250000000000000 : ℝ) by norm_num, show 1+2*(8889333954185849/100000000000000000000 : ℝ)=(50008889333954185849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1717540293631691/6250000000000000000 : ℝ)+(8889333954185849/100000000000000000000 : ℝ) ≤ ((284679831834753007/284750000000000000 : ℝ)+(43376371307/34170000000000 : ℝ)*((14757/100000 : ℝ)+(567/5000 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (284679831834753007/284750000000000000 : ℝ)+(43376371307/34170000000000 : ℝ)*((14757/100000 : ℝ)+(567/5000 : ℝ))=(1000084862504839/1000000000000000 : ℝ) by norm_num, show 1+(1717540293631691/6250000000000000000 : ℝ)+(8889333954185849/100000000000000000000 : ℝ)=(20007273995730458581/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1717540293631691/6250000000000000000 : ℝ) ≤ ((284679831834753007/284750000000000000 : ℝ)+2*(43376371307/34170000000000 : ℝ)*(14757/100000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (284679831834753007/284750000000000000 : ℝ)+2*(43376371307/34170000000000 : ℝ)*(14757/100000 : ℝ)=(500064119438073/500000000000000 : ℝ) by norm_num, show 1+2*(1717540293631691/6250000000000000000 : ℝ)=(3126717540293631691/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (284679831834753007/284750000000000000 : ℝ)*(X 1 0+X 2 0)+(43376371307/34170000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (284679831834753007/284750000000000000 : ℝ)) (alpha := (43376371307/34170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (284679831834753007/284750000000000000 : ℝ)*(X 0 1+X 2 1)+(43376371307/34170000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (284679831834753007/284750000000000000 : ℝ)) (alpha := (43376371307/34170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (284679831834753007/284750000000000000 : ℝ)*(X 0 2+X 1 2)+(43376371307/34170000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (284679831834753007/284750000000000000 : ℝ)) (alpha := (43376371307/34170000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-905232127/5000000000 : ℝ)*X 0 0+(1077251793/2000000000 : ℝ)*X 0 1+(5386259457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286062639/10000000000 : ℝ)*X 1 0+(-1948120411/10000000000 : ℝ)*X 1 1+(538625917/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286062841/10000000000 : ℝ)*X 2 0+(5386259093/10000000000 : ℝ)*X 2 1+(-1948120243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4450678527/10000000000 : ℝ)*X 0 0+(2117465767/5000000000 : ℝ)*X 0 1+(4234931413/10000000000 : ℝ)*X 0 2+(4450678527/10000000000 : ℝ)*X 1 0+(2117465767/5000000000 : ℝ)*X 1 1+(4234931413/10000000000 : ℝ)*X 1 2+(4450678527/10000000000 : ℝ)*X 2 0+(2117465767/5000000000 : ℝ)*X 2 1+(4234931413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213453483/1000000000 : ℝ)*X 0 0+(5266523291/10000000000 : ℝ)*X 0 1+(2633261739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684930111/5000000000 : ℝ)*X 1 0+(-199673407/1000000000 : ℝ)*X 1 1+(1316630721/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684929779/5000000000 : ℝ)*X 2 0+(5266524103/10000000000 : ℝ)*X 2 1+(-199673333/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((415702189/1000000000 : ℝ)*X 0 0+(1095427147/2500000000 : ℝ)*X 0 1+(4381709193/10000000000 : ℝ)*X 0 2+(415702189/1000000000 : ℝ)*X 1 0+(1095427147/2500000000 : ℝ)*X 1 1+(4381709193/10000000000 : ℝ)*X 1 2+(415702189/1000000000 : ℝ)*X 2 0+(1095427147/2500000000 : ℝ)*X 2 1+(4381709193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2066276061/10000000000 : ℝ)*X 0 0+(2591851311/5000000000 : ℝ)*X 0 1+(5400233891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276278557/10000000000 : ℝ)*X 1 0+(-1942320271/10000000000 : ℝ)*X 1 1+(1350058409/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276278421/10000000000 : ℝ)*X 2 0+(4320187/8000000 : ℝ)*X 2 1+(-19423203/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4484395321/10000000000 : ℝ)*X 0 0+(4217785683/10000000000 : ℝ)*X 0 1+(843557247/2000000000 : ℝ)*X 0 2+(4484395321/10000000000 : ℝ)*X 1 0+(4217785683/10000000000 : ℝ)*X 1 1+(843557247/2000000000 : ℝ)*X 1 2+(4484395321/10000000000 : ℝ)*X 2 0+(4217785683/10000000000 : ℝ)*X 2 1+(843557247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-29357869/156250000 : ℝ)*X 0 0+(5467055779/10000000000 : ℝ)*X 0 1+(5255397041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075528989/2000000000 : ℝ)*X 1 0+(-2001152309/10000000000 : ℝ)*X 1 1+(5255396511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377645877/10000000000 : ℝ)*X 2 0+(1313849147/2500000000 : ℝ)*X 2 1+(-1000575473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((258080261/625000000 : ℝ)*X 0 0+(879067403/2000000000 : ℝ)*X 0 1+(4395337051/10000000000 : ℝ)*X 0 2+(258080261/625000000 : ℝ)*X 1 0+(879067403/2000000000 : ℝ)*X 1 1+(4395337051/10000000000 : ℝ)*X 1 2+(258080261/625000000 : ℝ)*X 2 0+(879067403/2000000000 : ℝ)*X 2 1+(4395337051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-629/1000 : ℝ) ≤ (-2238740869990383118199403566493/3559375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63495447/100000000000000 : ℝ)*(lower1) + (108714497/100000000000000 : ℝ)*(lower2) + (83581859/50000000000000 : ℝ)*(lower3) + (24302691/50000000000000 : ℝ)*(lower4) + (754162577612611/25000000000000 : ℝ)*(major0) + (754162577612611/25000000000000 : ℝ)*(major1) + (754162577612611/25000000000000 : ℝ)*(major2) + (2978710977/25000000000000 : ℝ)*(sp1) + (829401300776363/20000000000000 : ℝ)*(sp4) + (2073497294518953/50000000000000 : ℝ)*(sp5) + (4146703887414481/100000000000000 : ℝ)*(sp6) + (1907228486142401/100000000000000 : ℝ)*(sp7) + (302616467333/100000000000000 : ℝ)*(sp14) + (31304812769/100000000000000 : ℝ)*(sp15) + (190725979095517/10000000000000 : ℝ)*(f.failure) + (829401300776363/20000000000000 : ℝ)*(f.sum) + (2810270185789/427125000000000000000000000 : ℝ)*base66 + (116060643701438831/21356250000000000000000000000000 : ℝ)*base67 + (15829105836451331/21356250000000000000000000000000 : ℝ)*base69 + (236512198254376331/21356250000000000000000000000000 : ℝ)*base71 + (2766194262539/3417000000000000000000000000 : ℝ)*base74 + (32031565340213831/21356250000000000000000000000000 : ℝ)*base75 + (192882082231782581/21356250000000000000000000000000 : ℝ)*base77 + (193145127227101331/21356250000000000000000000000000 : ℝ)*base79 + (1925908333771/106781250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12119209/1000000000000000000000 : ℝ)*base90 + (12119209/1000000000000000000000 : ℝ)*base92 + (12119209/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59113/100000 : ℝ) ≤ (2104144931411770079833987889213/3559375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30070713/100000000000000 : ℝ)*(lower3) + (92012069/100000000000000 : ℝ)*(upper4) + (1591887/12500000000000 : ℝ)*(upper5) + (1544132098139597/50000000000000 : ℝ)*(major0) + (1544132098139597/50000000000000 : ℝ)*(major1) + (1544132098139597/50000000000000 : ℝ)*(major2) + (32845939068263/781250000000 : ℝ)*(sp0) + (525534361806583/12500000000000 : ℝ)*(sp1) + (2102141068220991/50000000000000 : ℝ)*(sp2) + (488134187518053/25000000000000 : ℝ)*(sp3) + (507893987/100000000000000 : ℝ)*(sp7) + (5524546613/50000000000000 : ℝ)*(sp9) + (3807103909/100000000000000 : ℝ)*(sp10) + (2871404113/50000000000000 : ℝ)*(sp12) + (1952537257966199/100000000000000 : ℝ)*(f.failure) + (420428594354589/10000000000000 : ℝ)*(f.sum) + (2058239453261/1708500000000000000000000000 : ℝ)*base65 + (494989323878704537/42712500000000000000000000000000 : ℝ)*base67 + (167966347619817037/42712500000000000000000000000000 : ℝ)*base69 + (194133025830979537/42712500000000000000000000000000 : ℝ)*base71 + (13863418965239/1708500000000000000000000000 : ℝ)*base73 + (129570761468142037/42712500000000000000000000000000 : ℝ)*base75 + (79306563488282963/42712500000000000000000000000000 : ℝ)*base78 + (94432555500529537/42712500000000000000000000000000 : ℝ)*base79 + (10067305918459/3417000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (59404123/10000000000000000000000 : ℝ)*base90 + (59404123/10000000000000000000000 : ℝ)*base92 + (59404123/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2514/3125 : ℝ) ≤ (286354938588237456652572198089/355937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (97798793/100000000000000 : ℝ)*(upper0) + (1078489/50000000000000 : ℝ)*(upper1) + (46802581/100000000000000 : ℝ)*(upper2) + (21225924185723/625000000000 : ℝ)*(major0) + (21225924185723/625000000000 : ℝ)*(major1) + (21225924185723/625000000000 : ℝ)*(major2) + (198467327/5000000000000 : ℝ)*(sp0) + (1635874067/10000000000000 : ℝ)*(sp2) + (34866568421/100000000000000 : ℝ)*(sp3) + (1154568066229009/25000000000000 : ℝ)*(sp8) + (1154570958329447/25000000000000 : ℝ)*(sp9) + (2309133737288559/50000000000000 : ℝ)*(sp10) + (1073580035671279/50000000000000 : ℝ)*(sp11) + (1899763803/25000000000000 : ℝ)*(sp12) + (107359746895549/5000000000000 : ℝ)*(f.failure) + (1154570958329447/25000000000000 : ℝ)*(f.sum) + (9065014936091/3417000000000000000000000000 : ℝ)*base65 + (3149794237076567/533906250000000000000000000000 : ℝ)*base68 + (11565103015750643/2135625000000000000000000000000 : ℝ)*base70 + (9898692660719393/2135625000000000000000000000000 : ℝ)*base72 + (53174831053/170850000000000000000000000 : ℝ)*base73 + (2033522017661857/2135625000000000000000000000000 : ℝ)*base75 + (5745205789934393/2135625000000000000000000000000 : ℝ)*base78 + (7392277983493759/1067812500000000000000000000000 : ℝ)*base80 + (14996944854839/3417000000000000000000000000 : ℝ)*base81 + (8615927/500000000000000000000 : ℝ)*base89 + (8615927/500000000000000000000 : ℝ)*base91 + (8615927/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-16937/20000 : ℝ) ≤ (-177303772199573152949795659419/209375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234809277/100000000000000 : ℝ)*(lower1) + (708108081/100000000000000 : ℝ)*(lower2) + (66237213/25000000000000 : ℝ)*(upper5) + (858406654307113/25000000000000 : ℝ)*(major0) + (858406654307113/25000000000000 : ℝ)*(major1) + (858406654307113/25000000000000 : ℝ)*(major2) + (21405780281/100000000000000 : ℝ)*(sp0) + (343927783733/50000000000000 : ℝ)*(sp5) + (13752337431/4000000000000 : ℝ)*(sp6) + (96342032139/50000000000000 : ℝ)*(sp7) + (4724568634648731/100000000000000 : ℝ)*(sp12) + (2361951092430773/50000000000000 : ℝ)*(sp13) + (4724246231993237/100000000000000 : ℝ)*(sp14) + (1085348988092217/50000000000000 : ℝ)*(sp15) + (271361332531089/12500000000000 : ℝ)*(f.failure) + (1181147510107253/25000000000000 : ℝ)*(f.sum) + (50611522211/4020000000000000000000000 : ℝ)*base66 + (4248287973484331/1256250000000000000000000000000 : ℝ)*base68 + (2763767137840669/1256250000000000000000000000000 : ℝ)*base69 + (4740677450028169/1256250000000000000000000000000 : ℝ)*base71 + (66657400133/6281250000000000000000000 : ℝ)*base74 + (4787352775578169/1256250000000000000000000000000 : ℝ)*base75 + (6032041764203081/1256250000000000000000000000000 : ℝ)*base78 + (5639876164221919/1256250000000000000000000000000 : ℝ)*base79 + (50873371337/50250000000000000000000000 : ℝ)*base81 + (7248653/1250000000000000000000 : ℝ)*base90 + (7248653/1250000000000000000000 : ℝ)*base92 + (7248653/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1429_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(629/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(59113/100000 : ℝ) else (2514/3125 : ℝ) ≤ X j i ∧ X j i ≤ (16937/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1429_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1429_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(629/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(59113/100000 : ℝ) else (2514/3125 : ℝ) ≤ X j i ∧ X j i ≤ (16937/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1429_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1429_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(629/1000 : ℝ) ≤ X j i ∧ X j i ≤ -(59113/100000 : ℝ) else (2514/3125 : ℝ) ≤ X j i ∧ X j i ≤ (16937/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
