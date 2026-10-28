-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:03.305037+00:00
-- url     : https://prove2.me/submissions/5c04cefb-4650-48cb-b3b0-a3c7658af47e

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
theorem support_rectangle_w1249_s6_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116727639/10000000000 : ℝ)*x 0 + (2695625799/5000000000 : ℝ)*x 1 + (5267133297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116727639/10000000000 : ℝ)^4221 ≤ (12872867054197/100000000000000 : ℝ)^3197 := by
    have hnat : (2116727639 : ℕ)^4221*100000000000000^3197 ≤ 12872867054197^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116727639 10000000000 12872867054197 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695625799/5000000000 : ℝ)^4221 ≤ (2211666845139/5000000000000 : ℝ)^3197 := by
    have hnat : (2695625799 : ℕ)^4221*5000000000000^3197 ≤ 2211666845139^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695625799 5000000000 2211666845139 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267133297/10000000000 : ℝ)^4221 ≤ (42893796023699/100000000000000 : ℝ)^3197 := by
    have hnat : (5267133297 : ℕ)^4221*100000000000000^3197 ≤ 42893796023699^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267133297 10000000000 42893796023699 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116727639/10000000000 : ℝ), (2695625799/5000000000 : ℝ), (5267133297/10000000000 : ℝ)] ![(12872867054197/100000000000000 : ℝ), (2211666845139/5000000000000 : ℝ), (42893796023699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116727639/10000000000 : ℝ)|^4221 ≤ (12872867054197/100000000000000 : ℝ)^3197
        have hw : |(-2116727639/10000000000 : ℝ)|=(2116727639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695625799/5000000000 : ℝ)|^4221 ≤ (2211666845139/5000000000000 : ℝ)^3197
        have hw : |(2695625799/5000000000 : ℝ)|=(2695625799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267133297/10000000000 : ℝ)|^4221 ≤ (42893796023699/100000000000000 : ℝ)^3197
        have hw : |(5267133297/10000000000 : ℝ)|=(5267133297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334019911/625000000 : ℝ)*x 0 + (-544914927/2500000000 : ℝ)*x 1 + (5267133293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334019911/625000000 : ℝ)^4221 ≤ (10931410081661/25000000000000 : ℝ)^3197 := by
    have hnat : (334019911 : ℕ)^4221*25000000000000^3197 ≤ 10931410081661^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334019911 625000000 10931410081661 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544914927/2500000000 : ℝ)^4221 ≤ (13380563680529/100000000000000 : ℝ)^3197 := by
    have hnat : (544914927 : ℕ)^4221*100000000000000^3197 ≤ 13380563680529^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544914927 2500000000 13380563680529 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267133293/10000000000 : ℝ)^4221 ≤ (42893795980691/100000000000000 : ℝ)^3197 := by
    have hnat : (5267133293 : ℕ)^4221*100000000000000^3197 ≤ 42893795980691^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267133293 10000000000 42893795980691 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334019911/625000000 : ℝ), (-544914927/2500000000 : ℝ), (5267133293/10000000000 : ℝ)] ![(10931410081661/25000000000000 : ℝ), (13380563680529/100000000000000 : ℝ), (42893795980691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334019911/625000000 : ℝ)|^4221 ≤ (10931410081661/25000000000000 : ℝ)^3197
        have hw : |(334019911/625000000 : ℝ)|=(334019911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544914927/2500000000 : ℝ)|^4221 ≤ (13380563680529/100000000000000 : ℝ)^3197
        have hw : |(-544914927/2500000000 : ℝ)|=(544914927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267133293/10000000000 : ℝ)|^4221 ≤ (42893795980691/100000000000000 : ℝ)^3197
        have hw : |(5267133293/10000000000 : ℝ)|=(5267133293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344318583/10000000000 : ℝ)*x 0 + (1316783323/2500000000 : ℝ)*x 1 + (-2179659699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344318583/10000000000 : ℝ)^4221 ≤ (2186282020113/5000000000000 : ℝ)^3197 := by
    have hnat : (5344318583 : ℕ)^4221*5000000000000^3197 ≤ 2186282020113^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344318583 10000000000 2186282020113 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316783323/2500000000 : ℝ)^4221 ≤ (42893795969939/100000000000000 : ℝ)^3197 := by
    have hnat : (1316783323 : ℕ)^4221*100000000000000^3197 ≤ 42893795969939^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316783323 2500000000 42893795969939 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179659699/10000000000 : ℝ)^4221 ≤ (13380563607583/100000000000000 : ℝ)^3197 := by
    have hnat : (2179659699 : ℕ)^4221*100000000000000^3197 ≤ 13380563607583^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179659699 10000000000 13380563607583 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344318583/10000000000 : ℝ), (1316783323/2500000000 : ℝ), (-2179659699/10000000000 : ℝ)] ![(2186282020113/5000000000000 : ℝ), (42893795969939/100000000000000 : ℝ), (13380563607583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344318583/10000000000 : ℝ)|^4221 ≤ (2186282020113/5000000000000 : ℝ)^3197
        have hw : |(5344318583/10000000000 : ℝ)|=(5344318583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316783323/2500000000 : ℝ)|^4221 ≤ (42893795969939/100000000000000 : ℝ)^3197
        have hw : |(1316783323/2500000000 : ℝ)|=(1316783323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179659699/10000000000 : ℝ)|^4221 ≤ (13380563607583/100000000000000 : ℝ)^3197
        have hw : |(-2179659699/10000000000 : ℝ)|=(2179659699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349804933/10000000000 : ℝ)*x 0 + (4225516523/10000000000 : ℝ)*x 1 + (4477639619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349804933/10000000000 : ℝ)^4221 ≤ (33317434352927/100000000000000 : ℝ)^3197 := by
    have hnat : (4349804933 : ℕ)^4221*100000000000000^3197 ≤ 33317434352927^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349804933 10000000000 33317434352927 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225516523/10000000000 : ℝ)^4221 ≤ (32066310994343/100000000000000 : ℝ)^3197 := by
    have hnat : (4225516523 : ℕ)^4221*100000000000000^3197 ≤ 32066310994343^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225516523 10000000000 32066310994343 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477639619/10000000000 : ℝ)^4221 ≤ (34616254636553/100000000000000 : ℝ)^3197 := by
    have hnat : (4477639619 : ℕ)^4221*100000000000000^3197 ≤ 34616254636553^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477639619 10000000000 34616254636553 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349804933/10000000000 : ℝ), (4225516523/10000000000 : ℝ), (4477639619/10000000000 : ℝ)] ![(33317434352927/100000000000000 : ℝ), (32066310994343/100000000000000 : ℝ), (34616254636553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349804933/10000000000 : ℝ)|^4221 ≤ (33317434352927/100000000000000 : ℝ)^3197
        have hw : |(4349804933/10000000000 : ℝ)|=(4349804933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225516523/10000000000 : ℝ)|^4221 ≤ (32066310994343/100000000000000 : ℝ)^3197
        have hw : |(4225516523/10000000000 : ℝ)|=(4225516523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477639619/10000000000 : ℝ)|^4221 ≤ (34616254636553/100000000000000 : ℝ)^3197
        have hw : |(4477639619/10000000000 : ℝ)|=(4477639619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058366299/5000000000 : ℝ)*x 0 + (5267446903/10000000000 : ℝ)*x 1 + (2695468321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058366299/5000000000 : ℝ)^4221 ≤ (1609113359/12500000000 : ℝ)^3197 := by
    have hnat : (1058366299 : ℕ)^4221*12500000000^3197 ≤ 1609113359^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058366299 5000000000 1609113359 12500000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267446903/10000000000 : ℝ)^4221 ≤ (42897167975771/100000000000000 : ℝ)^3197 := by
    have hnat : (5267446903 : ℕ)^4221*100000000000000^3197 ≤ 42897167975771^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267446903 10000000000 42897167975771 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695468321/5000000000 : ℝ)^4221 ≤ (44229925141453/100000000000000 : ℝ)^3197 := by
    have hnat : (2695468321 : ℕ)^4221*100000000000000^3197 ≤ 44229925141453^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695468321 5000000000 44229925141453 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058366299/5000000000 : ℝ), (5267446903/10000000000 : ℝ), (2695468321/5000000000 : ℝ)] ![(1609113359/12500000000 : ℝ), (42897167975771/100000000000000 : ℝ), (44229925141453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058366299/5000000000 : ℝ)|^4221 ≤ (1609113359/12500000000 : ℝ)^3197
        have hw : |(-1058366299/5000000000 : ℝ)|=(1058366299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267446903/10000000000 : ℝ)|^4221 ≤ (42897167975771/100000000000000 : ℝ)^3197
        have hw : |(5267446903/10000000000 : ℝ)|=(5267446903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695468321/5000000000 : ℝ)|^4221 ≤ (44229925141453/100000000000000 : ℝ)^3197
        have hw : |(2695468321/5000000000 : ℝ)|=(2695468321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332039669/625000000 : ℝ)*x 0 + (-205585633/1000000000 : ℝ)*x 1 + (2695468099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332039669/625000000 : ℝ)^4221 ≤ (8676741355859/20000000000000 : ℝ)^3197 := by
    have hnat : (332039669 : ℕ)^4221*20000000000000^3197 ≤ 8676741355859^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332039669 625000000 8676741355859 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205585633/1000000000 : ℝ)^4221 ≤ (6193186435101/50000000000000 : ℝ)^3197 := by
    have hnat : (205585633 : ℕ)^4221*50000000000000^3197 ≤ 6193186435101^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205585633 1000000000 6193186435101 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695468099/5000000000 : ℝ)^4221 ≤ (44229920331867/100000000000000 : ℝ)^3197 := by
    have hnat : (2695468099 : ℕ)^4221*100000000000000^3197 ≤ 44229920331867^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695468099 5000000000 44229920331867 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332039669/625000000 : ℝ), (-205585633/1000000000 : ℝ), (2695468099/5000000000 : ℝ)] ![(8676741355859/20000000000000 : ℝ), (6193186435101/50000000000000 : ℝ), (44229920331867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332039669/625000000 : ℝ)|^4221 ≤ (8676741355859/20000000000000 : ℝ)^3197
        have hw : |(332039669/625000000 : ℝ)|=(332039669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205585633/1000000000 : ℝ)|^4221 ≤ (6193186435101/50000000000000 : ℝ)^3197
        have hw : |(-205585633/1000000000 : ℝ)|=(205585633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695468099/5000000000 : ℝ)|^4221 ≤ (44229920331867/100000000000000 : ℝ)^3197
        have hw : |(2695468099/5000000000 : ℝ)|=(2695468099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312634889/10000000000 : ℝ)*x 0 + (5390935889/10000000000 : ℝ)*x 1 + (-2055856501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312634889/10000000000 : ℝ)^4221 ≤ (271148179837/625000000000 : ℝ)^3197 := by
    have hnat : (5312634889 : ℕ)^4221*625000000000^3197 ≤ 271148179837^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312634889 10000000000 271148179837 625000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390935889/10000000000 : ℝ)^4221 ≤ (8845983396931/20000000000000 : ℝ)^3197 := by
    have hnat : (5390935889 : ℕ)^4221*20000000000000^3197 ≤ 8845983396931^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390935889 10000000000 8845983396931 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055856501/10000000000 : ℝ)^4221 ≤ (1548296778807/12500000000000 : ℝ)^3197 := by
    have hnat : (2055856501 : ℕ)^4221*12500000000000^3197 ≤ 1548296778807^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055856501 10000000000 1548296778807 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312634889/10000000000 : ℝ), (5390935889/10000000000 : ℝ), (-2055856501/10000000000 : ℝ)] ![(271148179837/625000000000 : ℝ), (8845983396931/20000000000000 : ℝ), (1548296778807/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312634889/10000000000 : ℝ)|^4221 ≤ (271148179837/625000000000 : ℝ)^3197
        have hw : |(5312634889/10000000000 : ℝ)|=(5312634889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390935889/10000000000 : ℝ)|^4221 ≤ (8845983396931/20000000000000 : ℝ)^3197
        have hw : |(5390935889/10000000000 : ℝ)|=(5390935889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055856501/10000000000 : ℝ)|^4221 ≤ (1548296778807/12500000000000 : ℝ)^3197
        have hw : |(-2055856501/10000000000 : ℝ)|=(2055856501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543726803/1250000000 : ℝ)*x 0 + (1119250473/2500000000 : ℝ)*x 1 + (4226156589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543726803/1250000000 : ℝ)^4221 ≤ (2082345645889/6250000000000 : ℝ)^3197 := by
    have hnat : (543726803 : ℕ)^4221*6250000000000^3197 ≤ 2082345645889^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543726803 1250000000 2082345645889 6250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119250473/2500000000 : ℝ)^4221 ≤ (4326218177811/12500000000000 : ℝ)^3197 := by
    have hnat : (1119250473 : ℕ)^4221*12500000000000^3197 ≤ 4326218177811^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119250473 2500000000 4326218177811 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226156589/10000000000 : ℝ)^4221 ≤ (16036362115049/50000000000000 : ℝ)^3197 := by
    have hnat : (4226156589 : ℕ)^4221*50000000000000^3197 ≤ 16036362115049^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226156589 10000000000 16036362115049 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543726803/1250000000 : ℝ), (1119250473/2500000000 : ℝ), (4226156589/10000000000 : ℝ)] ![(2082345645889/6250000000000 : ℝ), (4326218177811/12500000000000 : ℝ), (16036362115049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543726803/1250000000 : ℝ)|^4221 ≤ (2082345645889/6250000000000 : ℝ)^3197
        have hw : |(543726803/1250000000 : ℝ)|=(543726803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119250473/2500000000 : ℝ)|^4221 ≤ (4326218177811/12500000000000 : ℝ)^3197
        have hw : |(1119250473/2500000000 : ℝ)|=(1119250473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226156589/10000000000 : ℝ)|^4221 ≤ (16036362115049/50000000000000 : ℝ)^3197
        have hw : |(4226156589/10000000000 : ℝ)|=(4226156589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s6_8 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38152979/10000000000 : ℝ)*x 0 + (2956350479/5000000000 : ℝ)*x 1 + (5912755241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38152979/10000000000 : ℝ)^4221 ≤ (64104916131/100000000000000 : ℝ)^3197 := by
    have hnat : (38152979 : ℕ)^4221*100000000000000^3197 ≤ 64104916131^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38152979 10000000000 64104916131 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2956350479/5000000000 : ℝ)^4221 ≤ (12491911174433/25000000000000 : ℝ)^3197 := by
    have hnat : (2956350479 : ℕ)^4221*25000000000000^3197 ≤ 12491911174433^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956350479 5000000000 12491911174433 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5912755241/10000000000 : ℝ)^4221 ≤ (24984125186723/50000000000000 : ℝ)^3197 := by
    have hnat : (5912755241 : ℕ)^4221*50000000000000^3197 ≤ 24984125186723^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912755241 10000000000 24984125186723 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38152979/10000000000 : ℝ), (2956350479/5000000000 : ℝ), (5912755241/10000000000 : ℝ)] ![(64104916131/100000000000000 : ℝ), (12491911174433/25000000000000 : ℝ), (24984125186723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38152979/10000000000 : ℝ)|^4221 ≤ (64104916131/100000000000000 : ℝ)^3197
        have hw : |(-38152979/10000000000 : ℝ)|=(38152979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2956350479/5000000000 : ℝ)|^4221 ≤ (12491911174433/25000000000000 : ℝ)^3197
        have hw : |(2956350479/5000000000 : ℝ)|=(2956350479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5912755241/10000000000 : ℝ)|^4221 ≤ (24984125186723/50000000000000 : ℝ)^3197
        have hw : |(5912755241/10000000000 : ℝ)|=(5912755241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11483/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11463/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (6634233447733971/50000000000000000000 : ℝ) := by
    have hpowers : (11463/100000 : ℝ)^8441 ≤ (6634233447733971/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11463 : ℕ)^8441*50000000000000000000^2048 ≤ 6634233447733971^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11463 100000 6634233447733971 50000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11463/100000 : ℝ)) (X := (6634233447733971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14133/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (157250200349217/500000000000000000 : ℝ) := by
    have hpowers : (14133/100000 : ℝ)^8441 ≤ (157250200349217/500000000000000000 : ℝ)^2048 := by
      have hnat : (14133 : ℕ)^8441*500000000000000000^2048 ≤ 157250200349217^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14133 100000 157250200349217 500000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14133/100000 : ℝ)) (X := (157250200349217/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006634233447733971/25000000000000000000 : ℝ) ≤ (62504023677567/62500000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (25006634233447733971/25000000000000000000 : ℝ)^2048 ≤ (62504023677567/62500000000000 : ℝ)^8441 := by
      have hnat : (25006634233447733971 : ℕ)^2048*62500000000000^8441 ≤ 62504023677567^8441*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006634233447733971 25000000000000000000 62504023677567 62500000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62504023677567/62500000000000 : ℝ)) (X := (25006634233447733971/25000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022359253482655671/50000000000000000000 : ℝ) ≤ (10001084800346771/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50022359253482655671/50000000000000000000 : ℝ)^2048 ≤ (10001084800346771/10000000000000000 : ℝ)^8441 := by
      have hnat : (50022359253482655671 : ℕ)^2048*10000000000000000^8441 ≤ 10001084800346771^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022359253482655671 50000000000000000000 10001084800346771 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001084800346771/10000000000000000 : ℝ)) (X := (50022359253482655671/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (250157250200349217/250000000000000000 : ℝ) ≤ (5000762906141411/5000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (250157250200349217/250000000000000000 : ℝ)^2048 ≤ (5000762906141411/5000000000000000 : ℝ)^8441 := by
      have hnat : (250157250200349217 : ℕ)^2048*5000000000000000^8441 ≤ 5000762906141411^8441*250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250157250200349217 250000000000000000 5000762906141411 5000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000762906141411/5000000000000000 : ℝ)) (X := (250157250200349217/250000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6634233447733971/50000000000000000000 : ℝ) ≤ ((4448601379235119529/4450000000000000000 : ℝ)+2*(441011936051/267000000000000 : ℝ)*(11463/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (4448601379235119529/4450000000000000000 : ℝ)+2*(441011936051/267000000000000 : ℝ)*(11463/100000 : ℝ)=(62504023677567/62500000000000 : ℝ) by norm_num, show 1+2*(6634233447733971/50000000000000000000 : ℝ)=(25006634233447733971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157250200349217/500000000000000000 : ℝ)+(6634233447733971/50000000000000000000 : ℝ) ≤ ((4448601379235119529/4450000000000000000 : ℝ)+(441011936051/267000000000000 : ℝ)*((14133/100000 : ℝ)+(11463/100000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (4448601379235119529/4450000000000000000 : ℝ)+(441011936051/267000000000000 : ℝ)*((14133/100000 : ℝ)+(11463/100000 : ℝ))=(10001084800346771/10000000000000000 : ℝ) by norm_num, show 1+(157250200349217/500000000000000000 : ℝ)+(6634233447733971/50000000000000000000 : ℝ)=(50022359253482655671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157250200349217/500000000000000000 : ℝ) ≤ ((4448601379235119529/4450000000000000000 : ℝ)+2*(441011936051/267000000000000 : ℝ)*(14133/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (4448601379235119529/4450000000000000000 : ℝ)+2*(441011936051/267000000000000 : ℝ)*(14133/100000 : ℝ)=(5000762906141411/5000000000000000 : ℝ) by norm_num, show 1+2*(157250200349217/500000000000000000 : ℝ)=(250157250200349217/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4448601379235119529/4450000000000000000 : ℝ)*(X 1 0+X 2 0)+(441011936051/267000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (4448601379235119529/4450000000000000000 : ℝ)) (alpha := (441011936051/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4448601379235119529/4450000000000000000 : ℝ)*(X 0 1+X 2 1)+(441011936051/267000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (4448601379235119529/4450000000000000000 : ℝ)) (alpha := (441011936051/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4448601379235119529/4450000000000000000 : ℝ)*(X 0 2+X 1 2)+(441011936051/267000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11463/100000 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (4448601379235119529/4450000000000000000 : ℝ)) (alpha := (441011936051/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116727639/10000000000 : ℝ)*X 0 0+(2695625799/5000000000 : ℝ)*X 0 1+(5267133297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334019911/625000000 : ℝ)*X 1 0+(-544914927/2500000000 : ℝ)*X 1 1+(5267133293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344318583/10000000000 : ℝ)*X 2 0+(1316783323/2500000000 : ℝ)*X 2 1+(-2179659699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349804933/10000000000 : ℝ)*X 0 0+(4225516523/10000000000 : ℝ)*X 0 1+(4477639619/10000000000 : ℝ)*X 0 2+(4349804933/10000000000 : ℝ)*X 1 0+(4225516523/10000000000 : ℝ)*X 1 1+(4477639619/10000000000 : ℝ)*X 1 2+(4349804933/10000000000 : ℝ)*X 2 0+(4225516523/10000000000 : ℝ)*X 2 1+(4477639619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058366299/5000000000 : ℝ)*X 0 0+(5267446903/10000000000 : ℝ)*X 0 1+(2695468321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332039669/625000000 : ℝ)*X 1 0+(-205585633/1000000000 : ℝ)*X 1 1+(2695468099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312634889/10000000000 : ℝ)*X 2 0+(5390935889/10000000000 : ℝ)*X 2 1+(-2055856501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543726803/1250000000 : ℝ)*X 0 0+(1119250473/2500000000 : ℝ)*X 0 1+(4226156589/10000000000 : ℝ)*X 0 2+(543726803/1250000000 : ℝ)*X 1 0+(1119250473/2500000000 : ℝ)*X 1 1+(4226156589/10000000000 : ℝ)*X 1 2+(543726803/1250000000 : ℝ)*X 2 0+(1119250473/2500000000 : ℝ)*X 2 1+(4226156589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38152979/10000000000 : ℝ)*X 0 0+(2956350479/5000000000 : ℝ)*X 0 1+(5912755241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (442843427029808655567544953/55625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417367869/100000000000000 : ℝ)*(lower2) + (159488879/100000000000000 : ℝ)*(lower3) + (416311747/100000000000000 : ℝ)*(lower4) + (1116127/1000000000000 : ℝ)*(lower5) + (3005787130006419/50000000000000 : ℝ)*(major0) + (3005787130006419/50000000000000 : ℝ)*(major1) + (3005787130006419/50000000000000 : ℝ)*(major2) + (1611365422236579/20000000000000 : ℝ)*(sp0) + (1007103003844243/12500000000000 : ℝ)*(sp1) + (4028411292010707/50000000000000 : ℝ)*(sp2) + (1983158708993133/50000000000000 : ℝ)*(sp3) + (106342361/1562500000000 : ℝ)*(sp5) + (4126321817/50000000000000 : ℝ)*(sp6) + (745096431/20000000000000 : ℝ)*(sp8) + (1983158708993133/50000000000000 : ℝ)*(f.failure) + (1007103854583131/12500000000000 : ℝ)*(f.sum) + (74031537323/2225000000000000000000000000 : ℝ)*base65 + (6545139445467341/2500000000000000000000000000000 : ℝ)*base68 + (26928284460467341/2500000000000000000000000000000 : ℝ)*base70 + (173057572745467341/2500000000000000000000000000000 : ℝ)*base72 + (11916436244773/2225000000000000000000000000 : ℝ)*base73 + (3722336995467341/2500000000000000000000000000000 : ℝ)*base76 + (114378737815467341/2500000000000000000000000000000 : ℝ)*base78 + (20057673519532659/2500000000000000000000000000000 : ℝ)*base79 + (12361398001473/2225000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base83 + (68229279/5000000000000000000000 : ℝ)*base90 + (68229279/5000000000000000000000 : ℝ)*base92 + (68229279/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578152621025490619757587493/222500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (343008117/50000000000000 : ℝ)*(lower2) + (5514711/3125000000000 : ℝ)*(lower3) + (134051179/25000000000000 : ℝ)*(lower4) + (18628129/3125000000000 : ℝ)*(lower5) + (6042232563313387/100000000000000 : ℝ)*(major0) + (6042232563313387/100000000000000 : ℝ)*(major1) + (6042232563313387/100000000000000 : ℝ)*(major2) + (10960665897/25000000000000 : ℝ)*(sp0) + (6594015763/100000000000000 : ℝ)*(sp3) + (8097869145761149/100000000000000 : ℝ)*(sp4) + (8097919881815497/100000000000000 : ℝ)*(sp5) + (8097919881815497/100000000000000 : ℝ)*(sp6) + (398653856418087/10000000000000 : ℝ)*(sp7) + (172334769/2500000000000 : ℝ)*(sp8) + (1993272579098317/50000000000000 : ℝ)*(f.failure) + (8097919881815497/100000000000000 : ℝ)*(f.sum) + (248180385750013/13350000000000000000000000000 : ℝ)*base66 + (8391865275610721/15000000000000000000000000000000 : ℝ)*base67 + (309836967660610721/15000000000000000000000000000000 : ℝ)*base69 + (152320700670610721/15000000000000000000000000000000 : ℝ)*base71 + (33966494960087/13350000000000000000000000000 : ℝ)*base73 + (465307828380610721/15000000000000000000000000000000 : ℝ)*base75 + (180282696495610721/15000000000000000000000000000000 : ℝ)*base77 + (286279786545610721/15000000000000000000000000000000 : ℝ)*base79 + (111824246969237/13350000000000000000000000000 : ℝ)*base81 + (48267071/5000000000000000000000 : ℝ)*base90 + (48267071/5000000000000000000000 : ℝ)*base92 + (48267071/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1249_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_s7_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132296509/625000000 : ℝ)*x 0 + (5391059921/10000000000 : ℝ)*x 1 + (5267314083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132296509/625000000 : ℝ)^4221 ≤ (12872999579587/100000000000000 : ℝ)^3197 := by
    have hnat : (132296509 : ℕ)^4221*100000000000000^3197 ≤ 12872999579587^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132296509 625000000 12872999579587 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391059921/10000000000 : ℝ)^4221 ≤ (8846252110759/20000000000000 : ℝ)^3197 := by
    have hnat : (5391059921 : ℕ)^4221*20000000000000^3197 ≤ 8846252110759^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391059921 10000000000 8846252110759 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267314083/10000000000 : ℝ)^4221 ≤ (42895739861717/100000000000000 : ℝ)^3197 := by
    have hnat : (5267314083 : ℕ)^4221*100000000000000^3197 ≤ 42895739861717^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267314083 10000000000 42895739861717 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132296509/625000000 : ℝ), (5391059921/10000000000 : ℝ), (5267314083/10000000000 : ℝ)] ![(12872999579587/100000000000000 : ℝ), (8846252110759/20000000000000 : ℝ), (42895739861717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132296509/625000000 : ℝ)|^4221 ≤ (12872999579587/100000000000000 : ℝ)^3197
        have hw : |(-132296509/625000000 : ℝ)|=(132296509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391059921/10000000000 : ℝ)|^4221 ≤ (8846252110759/20000000000000 : ℝ)^3197
        have hw : |(5391059921/10000000000 : ℝ)|=(5391059921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267314083/10000000000 : ℝ)|^4221 ≤ (42895739861717/100000000000000 : ℝ)^3197
        have hw : |(5267314083/10000000000 : ℝ)|=(5267314083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668033733/1250000000 : ℝ)*x 0 + (-2179484521/10000000000 : ℝ)*x 1 + (329207143/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668033733/1250000000 : ℝ)^4221 ≤ (21862557062693/50000000000000 : ℝ)^3197 := by
    have hnat : (668033733 : ℕ)^4221*50000000000000^3197 ≤ 21862557062693^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668033733 1250000000 21862557062693 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179484521/10000000000 : ℝ)^4221 ≤ (3344785947621/25000000000000 : ℝ)^3197 := by
    have hnat : (2179484521 : ℕ)^4221*25000000000000^3197 ≤ 3344785947621^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179484521 10000000000 3344785947621 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329207143/625000000 : ℝ)^4221 ≤ (33512298489/78125000000 : ℝ)^3197 := by
    have hnat : (329207143 : ℕ)^4221*78125000000^3197 ≤ 33512298489^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329207143 625000000 33512298489 78125000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668033733/1250000000 : ℝ), (-2179484521/10000000000 : ℝ), (329207143/625000000 : ℝ)] ![(21862557062693/50000000000000 : ℝ), (3344785947621/25000000000000 : ℝ), (33512298489/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668033733/1250000000 : ℝ)|^4221 ≤ (21862557062693/50000000000000 : ℝ)^3197
        have hw : |(668033733/1250000000 : ℝ)|=(668033733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179484521/10000000000 : ℝ)|^4221 ≤ (3344785947621/25000000000000 : ℝ)^3197
        have hw : |(-2179484521/10000000000 : ℝ)|=(2179484521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329207143/625000000 : ℝ)|^4221 ≤ (33512298489/78125000000 : ℝ)^3197
        have hw : |(329207143/625000000 : ℝ)|=(329207143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106885397/200000000 : ℝ)*x 0 + (329207141/625000000 : ℝ)*x 1 + (-2179484583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106885397/200000000 : ℝ)^4221 ≤ (21862556987077/50000000000000 : ℝ)^3197 := by
    have hnat : (106885397 : ℕ)^4221*50000000000000^3197 ≤ 21862556987077^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106885397 200000000 21862556987077 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329207141/625000000 : ℝ)^4221 ≤ (42895741721849/100000000000000 : ℝ)^3197 := by
    have hnat : (329207141 : ℕ)^4221*100000000000000^3197 ≤ 42895741721849^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329207141 625000000 42895741721849 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179484583/10000000000 : ℝ)^4221 ≤ (13379144292987/100000000000000 : ℝ)^3197 := by
    have hnat : (2179484583 : ℕ)^4221*100000000000000^3197 ≤ 13379144292987^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179484583 10000000000 13379144292987 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106885397/200000000 : ℝ), (329207141/625000000 : ℝ), (-2179484583/10000000000 : ℝ)] ![(21862556987077/50000000000000 : ℝ), (42895741721849/100000000000000 : ℝ), (13379144292987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106885397/200000000 : ℝ)|^4221 ≤ (21862556987077/50000000000000 : ℝ)^3197
        have hw : |(106885397/200000000 : ℝ)|=(106885397/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329207141/625000000 : ℝ)|^4221 ≤ (42895741721849/100000000000000 : ℝ)^3197
        have hw : |(329207141/625000000 : ℝ)|=(329207141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179484583/10000000000 : ℝ)|^4221 ≤ (13379144292987/100000000000000 : ℝ)^3197
        have hw : |(-2179484583/10000000000 : ℝ)|=(2179484583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349814529/10000000000 : ℝ)*x 0 + (211294683/500000000 : ℝ)*x 1 + (4477259901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349814529/10000000000 : ℝ)^4221 ≤ (8329382849019/25000000000000 : ℝ)^3197 := by
    have hnat : (4349814529 : ℕ)^4221*25000000000000^3197 ≤ 8329382849019^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349814529 10000000000 8329382849019 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211294683/500000000 : ℝ)^4221 ≤ (32070089736523/100000000000000 : ℝ)^3197 := by
    have hnat : (211294683 : ℕ)^4221*100000000000000^3197 ≤ 32070089736523^3197*500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211294683 500000000 32070089736523 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477259901/10000000000 : ℝ)^4221 ≤ (17306189429057/50000000000000 : ℝ)^3197 := by
    have hnat : (4477259901 : ℕ)^4221*50000000000000^3197 ≤ 17306189429057^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477259901 10000000000 17306189429057 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349814529/10000000000 : ℝ), (211294683/500000000 : ℝ), (4477259901/10000000000 : ℝ)] ![(8329382849019/25000000000000 : ℝ), (32070089736523/100000000000000 : ℝ), (17306189429057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349814529/10000000000 : ℝ)|^4221 ≤ (8329382849019/25000000000000 : ℝ)^3197
        have hw : |(4349814529/10000000000 : ℝ)|=(4349814529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211294683/500000000 : ℝ)|^4221 ≤ (32070089736523/100000000000000 : ℝ)^3197
        have hw : |(211294683/500000000 : ℝ)|=(211294683/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477259901/10000000000 : ℝ)|^4221 ≤ (17306189429057/50000000000000 : ℝ)^3197
        have hw : |(4477259901/10000000000 : ℝ)|=(4477259901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116748823/10000000000 : ℝ)*x 0 + (5267626297/10000000000 : ℝ)*x 1 + (2695373273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116748823/10000000000 : ℝ)^4221 ≤ (51492148597/400000000000 : ℝ)^3197 := by
    have hnat : (2116748823 : ℕ)^4221*400000000000^3197 ≤ 51492148597^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116748823 10000000000 51492148597 400000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267626297/10000000000 : ℝ)^4221 ≤ (42899096883499/100000000000000 : ℝ)^3197 := by
    have hnat : (5267626297 : ℕ)^4221*100000000000000^3197 ≤ 42899096883499^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267626297 10000000000 42899096883499 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695373273/5000000000 : ℝ)^4221 ≤ (1382120811161/3125000000000 : ℝ)^3197 := by
    have hnat : (2695373273 : ℕ)^4221*3125000000000^3197 ≤ 1382120811161^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695373273 5000000000 1382120811161 3125000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116748823/10000000000 : ℝ), (5267626297/10000000000 : ℝ), (2695373273/5000000000 : ℝ)] ![(51492148597/400000000000 : ℝ), (42899096883499/100000000000000 : ℝ), (1382120811161/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116748823/10000000000 : ℝ)|^4221 ≤ (51492148597/400000000000 : ℝ)^3197
        have hw : |(-2116748823/10000000000 : ℝ)|=(2116748823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267626297/10000000000 : ℝ)|^4221 ≤ (42899096883499/100000000000000 : ℝ)^3197
        have hw : |(5267626297/10000000000 : ℝ)|=(5267626297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695373273/5000000000 : ℝ)|^4221 ≤ (1382120811161/3125000000000 : ℝ)^3197
        have hw : |(2695373273/5000000000 : ℝ)|=(2695373273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340327/5000000000 : ℝ)*x 0 + (-514013077/2500000000 : ℝ)*x 1 + (1078149309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340327/5000000000 : ℝ)^4221 ≤ (5423025275197/12500000000000 : ℝ)^3197 := by
    have hnat : (2656340327 : ℕ)^4221*12500000000000^3197 ≤ 5423025275197^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340327 5000000000 5423025275197 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514013077/2500000000 : ℝ)^4221 ≤ (12387931841269/100000000000000 : ℝ)^3197 := by
    have hnat : (514013077 : ℕ)^4221*100000000000000^3197 ≤ 12387931841269^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514013077 2500000000 12387931841269 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078149309/2000000000 : ℝ)^4221 ≤ (552848324329/1250000000000 : ℝ)^3197 := by
    have hnat : (1078149309 : ℕ)^4221*1250000000000^3197 ≤ 552848324329^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078149309 2000000000 552848324329 1250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340327/5000000000 : ℝ), (-514013077/2500000000 : ℝ), (1078149309/2000000000 : ℝ)] ![(5423025275197/12500000000000 : ℝ), (12387931841269/100000000000000 : ℝ), (552848324329/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340327/5000000000 : ℝ)|^4221 ≤ (5423025275197/12500000000000 : ℝ)^3197
        have hw : |(2656340327/5000000000 : ℝ)|=(2656340327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514013077/2500000000 : ℝ)|^4221 ≤ (12387931841269/100000000000000 : ℝ)^3197
        have hw : |(-514013077/2500000000 : ℝ)|=(514013077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078149309/2000000000 : ℝ)|^4221 ≤ (552848324329/1250000000000 : ℝ)^3197
        have hw : |(1078149309/2000000000 : ℝ)|=(1078149309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312680657/10000000000 : ℝ)*x 0 + (2695373273/5000000000 : ℝ)*x 1 + (-1028026151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312680657/10000000000 : ℝ)^4221 ≤ (21692101116961/50000000000000 : ℝ)^3197 := by
    have hnat : (5312680657 : ℕ)^4221*50000000000000^3197 ≤ 21692101116961^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312680657 10000000000 21692101116961 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695373273/5000000000 : ℝ)^4221 ≤ (1382120811161/3125000000000 : ℝ)^3197 := by
    have hnat : (2695373273 : ℕ)^4221*3125000000000^3197 ≤ 1382120811161^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695373273 5000000000 1382120811161 3125000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028026151/5000000000 : ℝ)^4221 ≤ (12387931793539/100000000000000 : ℝ)^3197 := by
    have hnat : (1028026151 : ℕ)^4221*100000000000000^3197 ≤ 12387931793539^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028026151 5000000000 12387931793539 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312680657/10000000000 : ℝ), (2695373273/5000000000 : ℝ), (-1028026151/5000000000 : ℝ)] ![(21692101116961/50000000000000 : ℝ), (1382120811161/3125000000000 : ℝ), (12387931793539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312680657/10000000000 : ℝ)|^4221 ≤ (21692101116961/50000000000000 : ℝ)^3197
        have hw : |(5312680657/10000000000 : ℝ)|=(5312680657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695373273/5000000000 : ℝ)|^4221 ≤ (1382120811161/3125000000000 : ℝ)^3197
        have hw : |(2695373273/5000000000 : ℝ)|=(2695373273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028026151/5000000000 : ℝ)|^4221 ≤ (12387931793539/100000000000000 : ℝ)^3197
        have hw : |(-1028026151/5000000000 : ℝ)|=(1028026151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s7_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349823761/10000000000 : ℝ)*x 0 + (4476625901/10000000000 : ℝ)*x 1 + (2113265077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349823761/10000000000 : ℝ)^4221 ≤ (16658812379101/50000000000000 : ℝ)^3197 := by
    have hnat : (4349823761 : ℕ)^4221*50000000000000^3197 ≤ 16658812379101^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349823761 10000000000 16658812379101 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476625901/10000000000 : ℝ)^4221 ≤ (8651476965021/25000000000000 : ℝ)^3197 := by
    have hnat : (4476625901 : ℕ)^4221*25000000000000^3197 ≤ 8651476965021^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476625901 10000000000 8651476965021 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113265077/5000000000 : ℝ)^4221 ≤ (3207646736353/10000000000000 : ℝ)^3197 := by
    have hnat : (2113265077 : ℕ)^4221*10000000000000^3197 ≤ 3207646736353^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113265077 5000000000 3207646736353 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349823761/10000000000 : ℝ), (4476625901/10000000000 : ℝ), (2113265077/5000000000 : ℝ)] ![(16658812379101/50000000000000 : ℝ), (8651476965021/25000000000000 : ℝ), (3207646736353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349823761/10000000000 : ℝ)|^4221 ≤ (16658812379101/50000000000000 : ℝ)^3197
        have hw : |(4349823761/10000000000 : ℝ)|=(4349823761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476625901/10000000000 : ℝ)|^4221 ≤ (8651476965021/25000000000000 : ℝ)^3197
        have hw : |(4476625901/10000000000 : ℝ)|=(4476625901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113265077/5000000000 : ℝ)|^4221 ≤ (3207646736353/10000000000000 : ℝ)^3197
        have hw : |(2113265077/5000000000 : ℝ)|=(2113265077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11483/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (1670517748954003/12500000000000000000 : ℝ) := by
    have hpowers : (11483/100000 : ℝ)^8441 ≤ (1670517748954003/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11483 : ℕ)^8441*12500000000000000000^2048 ≤ 1670517748954003^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11483 100000 1670517748954003 12500000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11483/100000 : ℝ)) (X := (1670517748954003/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (8441/2048 : ℝ) ≤ (15628940081066167/50000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^8441 ≤ (15628940081066167/50000000000000000000 : ℝ)^2048 := by
      have hnat : (441 : ℕ)^8441*50000000000000000000^2048 ≤ 15628940081066167^2048*3125^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 15628940081066167 50000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (15628940081066167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251670517748954003/6250000000000000000 : ℝ) ≤ (625040526882119/625000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (6251670517748954003/6250000000000000000 : ℝ)^2048 ≤ (625040526882119/625000000000000 : ℝ)^8441 := by
      have hnat : (6251670517748954003 : ℕ)^2048*625000000000000^8441 ≤ 625040526882119^8441*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251670517748954003 6250000000000000000 625040526882119 625000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040526882119/625000000000000 : ℝ)) (X := (6251670517748954003/6250000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022311011076882179/50000000000000000000 : ℝ) ≤ (2500270615043251/2500000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50022311011076882179/50000000000000000000 : ℝ)^2048 ≤ (2500270615043251/2500000000000000 : ℝ)^8441 := by
      have hnat : (50022311011076882179 : ℕ)^2048*2500000000000000^8441 ≤ 2500270615043251^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022311011076882179 50000000000000000000 2500270615043251 2500000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500270615043251/2500000000000000 : ℝ)) (X := (50022311011076882179/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015628940081066167/25000000000000000000 : ℝ) ≤ (1250189561279013/1250000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (25015628940081066167/25000000000000000000 : ℝ)^2048 ≤ (1250189561279013/1250000000000000 : ℝ)^8441 := by
      have hnat : (25015628940081066167 : ℕ)^2048*1250000000000000^8441 ≤ 1250189561279013^8441*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015628940081066167 25000000000000000000 1250189561279013 1250000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250189561279013/1250000000000000 : ℝ)) (X := (25015628940081066167/25000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1670517748954003/12500000000000000000 : ℝ) ≤ ((298656099868547307/298750000000000000 : ℝ)+2*(394572781/239000000000 : ℝ)*(11483/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (298656099868547307/298750000000000000 : ℝ)+2*(394572781/239000000000 : ℝ)*(11483/100000 : ℝ)=(625040526882119/625000000000000 : ℝ) by norm_num, show 1+2*(1670517748954003/12500000000000000000 : ℝ)=(6251670517748954003/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15628940081066167/50000000000000000000 : ℝ)+(1670517748954003/12500000000000000000 : ℝ) ≤ ((298656099868547307/298750000000000000 : ℝ)+(394572781/239000000000 : ℝ)*((441/3125 : ℝ)+(11483/100000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (298656099868547307/298750000000000000 : ℝ)+(394572781/239000000000 : ℝ)*((441/3125 : ℝ)+(11483/100000 : ℝ))=(2500270615043251/2500000000000000 : ℝ) by norm_num, show 1+(15628940081066167/50000000000000000000 : ℝ)+(1670517748954003/12500000000000000000 : ℝ)=(50022311011076882179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15628940081066167/50000000000000000000 : ℝ) ≤ ((298656099868547307/298750000000000000 : ℝ)+2*(394572781/239000000000 : ℝ)*(441/3125 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (298656099868547307/298750000000000000 : ℝ)+2*(394572781/239000000000 : ℝ)*(441/3125 : ℝ)=(1250189561279013/1250000000000000 : ℝ) by norm_num, show 1+2*(15628940081066167/50000000000000000000 : ℝ)=(25015628940081066167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (298656099868547307/298750000000000000 : ℝ)*(X 1 0+X 2 0)+(394572781/239000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11483/100000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (298656099868547307/298750000000000000 : ℝ)) (alpha := (394572781/239000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (298656099868547307/298750000000000000 : ℝ)*(X 0 1+X 2 1)+(394572781/239000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11483/100000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (298656099868547307/298750000000000000 : ℝ)) (alpha := (394572781/239000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (298656099868547307/298750000000000000 : ℝ)*(X 0 2+X 1 2)+(394572781/239000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11483/100000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (298656099868547307/298750000000000000 : ℝ)) (alpha := (394572781/239000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132296509/625000000 : ℝ)*X 0 0+(5391059921/10000000000 : ℝ)*X 0 1+(5267314083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668033733/1250000000 : ℝ)*X 1 0+(-2179484521/10000000000 : ℝ)*X 1 1+(329207143/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106885397/200000000 : ℝ)*X 2 0+(329207141/625000000 : ℝ)*X 2 1+(-2179484583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349814529/10000000000 : ℝ)*X 0 0+(211294683/500000000 : ℝ)*X 0 1+(4477259901/10000000000 : ℝ)*X 0 2+(4349814529/10000000000 : ℝ)*X 1 0+(211294683/500000000 : ℝ)*X 1 1+(4477259901/10000000000 : ℝ)*X 1 2+(4349814529/10000000000 : ℝ)*X 2 0+(211294683/500000000 : ℝ)*X 2 1+(4477259901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116748823/10000000000 : ℝ)*X 0 0+(5267626297/10000000000 : ℝ)*X 0 1+(2695373273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656340327/5000000000 : ℝ)*X 1 0+(-514013077/2500000000 : ℝ)*X 1 1+(1078149309/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312680657/10000000000 : ℝ)*X 2 0+(2695373273/5000000000 : ℝ)*X 2 1+(-1028026151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349823761/10000000000 : ℝ)*X 0 0+(4476625901/10000000000 : ℝ)*X 0 1+(2113265077/5000000000 : ℝ)*X 0 2+(4349823761/10000000000 : ℝ)*X 1 0+(4476625901/10000000000 : ℝ)*X 1 1+(2113265077/5000000000 : ℝ)*X 1 2+(4349823761/10000000000 : ℝ)*X 2 0+(4476625901/10000000000 : ℝ)*X 2 1+(2113265077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54632413142660039280857301/14937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2886181/312500000000 : ℝ)*(base19) + (156081313/20000000000000 : ℝ)*(base23) + (49182151/50000000000000 : ℝ)*(lower2) + (19494957/10000000000000 : ℝ)*(upper3) + (33163281/100000000000000 : ℝ)*(lower4) + (6029722765225927/100000000000000 : ℝ)*(major0) + (6029722765225927/100000000000000 : ℝ)*(major1) + (6029722765225927/100000000000000 : ℝ)*(major2) + (4040560463711271/50000000000000 : ℝ)*(sp0) + (8081153043328653/100000000000000 : ℝ)*(sp1) + (8081153186500009/100000000000000 : ℝ)*(sp2) + (159130915697977/4000000000000 : ℝ)*(sp3) + (258120969/781250000000 : ℝ)*(sp4) + (18549182511/100000000000000 : ℝ)*(sp7) + (62160803775499/1562500000000 : ℝ)*(f.failure) + (4040576983453287/50000000000000 : ℝ)*(f.sum) + (118373574043/59750000000000000000000000 : ℝ)*base65 + (94767475084196411/29875000000000000000000000000000 : ℝ)*base68 + (539850138924196411/29875000000000000000000000000000 : ℝ)*base70 + (35891656152821411/29875000000000000000000000000000 : ℝ)*base72 + (11258847459/119500000000000000000000000 : ℝ)*base73 + (346627051903446411/29875000000000000000000000000000 : ℝ)*base76 + (294245142960571411/29875000000000000000000000000000 : ℝ)*base78 + (1046791101171946411/29875000000000000000000000000000 : ℝ)*base80 + (7522400849/7468750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9637/156250000000000000000 : ℝ)*base90 + (9637/156250000000000000000 : ℝ)*base92 + (9637/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50138705328451539630814197/14937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150308533/25000000000000 : ℝ)*(base19) + (655887713/100000000000000 : ℝ)*(base23) + (13938019/20000000000000 : ℝ)*(upper3) + (20976341/100000000000000 : ℝ)*(lower4) + (64758093/100000000000000 : ℝ)*(upper5) + (6060304399864419/100000000000000 : ℝ)*(major0) + (6060304399864419/100000000000000 : ℝ)*(major1) + (6060304399864419/100000000000000 : ℝ)*(major2) + (4184921881/25000000000000 : ℝ)*(sp1) + (18519647097/100000000000000 : ℝ)*(sp2) + (507633755653937/6250000000000 : ℝ)*(sp4) + (1015265343692667/12500000000000 : ℝ)*(sp5) + (4061060457464091/50000000000000 : ℝ)*(sp6) + (3998468597380301/100000000000000 : ℝ)*(sp7) + (3998468597380301/100000000000000 : ℝ)*(f.failure) + (507633755653937/6250000000000 : ℝ)*(f.sum) + (11217120131/1912000000000000000000000 : ℝ)*base66 + (157836572810555367/29875000000000000000000000000000 : ℝ)*base68 + (488593009495430367/29875000000000000000000000000000 : ℝ)*base70 + (49370776076055367/29875000000000000000000000000000 : ℝ)*base72 + (838741268671/239000000000000000000000000 : ℝ)*base74 + (414873501320430367/29875000000000000000000000000000 : ℝ)*base76 + (281266816078055367/29875000000000000000000000000000 : ℝ)*base78 + (501613383513055367/29875000000000000000000000000000 : ℝ)*base80 + (1044128100741/239000000000000000000000000 : ℝ)*base82 + (47683263/10000000000000000000000 : ℝ)*base90 + (47683263/10000000000000000000000 : ℝ)*base92 + (47683263/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_box_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9966303/50000000 : ℝ)*x 0 + (2687369793/5000000000 : ℝ)*x 1 + (5374739539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9966303/50000000 : ℝ)^4221 ≤ (11890887238203/100000000000000 : ℝ)^3197 := by
    have hnat : (9966303 : ℕ)^4221*100000000000000^3197 ≤ 11890887238203^3197*50000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9966303 50000000 11890887238203 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687369793/5000000000 : ℝ)^4221 ≤ (11013639157703/25000000000000 : ℝ)^3197 := by
    have hnat : (2687369793 : ℕ)^4221*25000000000000^3197 ≤ 11013639157703^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687369793 5000000000 11013639157703 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374739539/10000000000 : ℝ)^4221 ≤ (2202727806109/5000000000000 : ℝ)^3197 := by
    have hnat : (5374739539 : ℕ)^4221*5000000000000^3197 ≤ 2202727806109^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374739539 10000000000 2202727806109 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9966303/50000000 : ℝ), (2687369793/5000000000 : ℝ), (5374739539/10000000000 : ℝ)] ![(11890887238203/100000000000000 : ℝ), (11013639157703/25000000000000 : ℝ), (2202727806109/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9966303/50000000 : ℝ)|^4221 ≤ (11890887238203/100000000000000 : ℝ)^3197
        have hw : |(-9966303/50000000 : ℝ)|=(9966303/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687369793/5000000000 : ℝ)|^4221 ≤ (11013639157703/25000000000000 : ℝ)^3197
        have hw : |(2687369793/5000000000 : ℝ)|=(2687369793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374739539/10000000000 : ℝ)|^4221 ≤ (2202727806109/5000000000000 : ℝ)^3197
        have hw : |(5374739539/10000000000 : ℝ)|=(5374739539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296840891/10000000000 : ℝ)*x 0 + (-524788189/2500000000 : ℝ)*x 1 + (1343684923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296840891/10000000000 : ℝ)^4221 ≤ (43213502901913/100000000000000 : ℝ)^3197 := by
    have hnat : (5296840891 : ℕ)^4221*100000000000000^3197 ≤ 43213502901913^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296840891 10000000000 43213502901913 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524788189/2500000000 : ℝ)^4221 ≤ (6365969654547/50000000000000 : ℝ)^3197 := by
    have hnat : (524788189 : ℕ)^4221*50000000000000^3197 ≤ 6365969654547^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524788189 2500000000 6365969654547 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343684923/2500000000 : ℝ)^4221 ≤ (2202727888897/5000000000000 : ℝ)^3197 := by
    have hnat : (1343684923 : ℕ)^4221*5000000000000^3197 ≤ 2202727888897^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343684923 2500000000 2202727888897 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296840891/10000000000 : ℝ), (-524788189/2500000000 : ℝ), (1343684923/2500000000 : ℝ)] ![(43213502901913/100000000000000 : ℝ), (6365969654547/50000000000000 : ℝ), (2202727888897/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296840891/10000000000 : ℝ)|^4221 ≤ (43213502901913/100000000000000 : ℝ)^3197
        have hw : |(5296840891/10000000000 : ℝ)|=(5296840891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524788189/2500000000 : ℝ)|^4221 ≤ (6365969654547/50000000000000 : ℝ)^3197
        have hw : |(-524788189/2500000000 : ℝ)|=(524788189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343684923/2500000000 : ℝ)|^4221 ≤ (2202727888897/5000000000000 : ℝ)^3197
        have hw : |(1343684923/2500000000 : ℝ)|=(1343684923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529684089/1000000000 : ℝ)*x 0 + (2687369907/5000000000 : ℝ)*x 1 + (-131197037/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529684089/1000000000 : ℝ)^4221 ≤ (43213502891141/100000000000000 : ℝ)^3197 := by
    have hnat : (529684089 : ℕ)^4221*100000000000000^3197 ≤ 43213502891141^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529684089 1000000000 43213502891141 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687369907/5000000000 : ℝ)^4221 ≤ (2202727954911/5000000000000 : ℝ)^3197 := by
    have hnat : (2687369907 : ℕ)^4221*5000000000000^3197 ≤ 2202727954911^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687369907 5000000000 2202727954911 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131197037/625000000 : ℝ)^4221 ≤ (1591492249473/12500000000000 : ℝ)^3197 := by
    have hnat : (131197037 : ℕ)^4221*12500000000000^3197 ≤ 1591492249473^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131197037 625000000 1591492249473 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529684089/1000000000 : ℝ), (2687369907/5000000000 : ℝ), (-131197037/625000000 : ℝ)] ![(43213502891141/100000000000000 : ℝ), (2202727954911/5000000000000 : ℝ), (1591492249473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529684089/1000000000 : ℝ)|^4221 ≤ (43213502891141/100000000000000 : ℝ)^3197
        have hw : |(529684089/1000000000 : ℝ)|=(529684089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687369907/5000000000 : ℝ)|^4221 ≤ (2202727954911/5000000000000 : ℝ)^3197
        have hw : |(2687369907/5000000000 : ℝ)|=(2687369907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131197037/625000000 : ℝ)|^4221 ≤ (1591492249473/12500000000000 : ℝ)^3197
        have hw : |(-131197037/625000000 : ℝ)|=(131197037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2228141413/5000000000 : ℝ)*x 0 + (4298619689/10000000000 : ℝ)*x 1 + (171944807/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228141413/5000000000 : ℝ)^4221 ≤ (2149901860281/6250000000000 : ℝ)^3197 := by
    have hnat : (2228141413 : ℕ)^4221*6250000000000^3197 ≤ 2149901860281^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228141413 5000000000 2149901860281 6250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298619689/10000000000 : ℝ)^4221 ≤ (1640039133151/5000000000000 : ℝ)^3197 := by
    have hnat : (4298619689 : ℕ)^4221*5000000000000^3197 ≤ 1640039133151^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298619689 10000000000 1640039133151 5000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171944807/400000000 : ℝ)^4221 ≤ (32800787559277/100000000000000 : ℝ)^3197 := by
    have hnat : (171944807 : ℕ)^4221*100000000000000^3197 ≤ 32800787559277^3197*400000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171944807 400000000 32800787559277 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228141413/5000000000 : ℝ), (4298619689/10000000000 : ℝ), (171944807/400000000 : ℝ)] ![(2149901860281/6250000000000 : ℝ), (1640039133151/5000000000000 : ℝ), (32800787559277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228141413/5000000000 : ℝ)|^4221 ≤ (2149901860281/6250000000000 : ℝ)^3197
        have hw : |(2228141413/5000000000 : ℝ)|=(2228141413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4298619689/10000000000 : ℝ)|^4221 ≤ (1640039133151/5000000000000 : ℝ)^3197
        have hw : |(4298619689/10000000000 : ℝ)|=(4298619689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171944807/400000000 : ℝ)|^4221 ≤ (32800787559277/100000000000000 : ℝ)^3197
        have hw : |(171944807/400000000 : ℝ)|=(171944807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-560403227/2500000000 : ℝ)*x 0 + (5282352873/10000000000 : ℝ)*x 1 + (5282352899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560403227/2500000000 : ℝ)^4221 ≤ (13884971802849/100000000000000 : ℝ)^3197 := by
    have hnat : (560403227 : ℕ)^4221*100000000000000^3197 ≤ 13884971802849^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560403227 2500000000 13884971802849 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282352873/10000000000 : ℝ)^4221 ≤ (8611502790263/20000000000000 : ℝ)^3197 := by
    have hnat : (5282352873 : ℕ)^4221*20000000000000^3197 ≤ 8611502790263^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282352873 10000000000 8611502790263 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282352899/10000000000 : ℝ)^4221 ≤ (5382189278891/12500000000000 : ℝ)^3197 := by
    have hnat : (5282352899 : ℕ)^4221*12500000000000^3197 ≤ 5382189278891^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282352899 10000000000 5382189278891 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-560403227/2500000000 : ℝ), (5282352873/10000000000 : ℝ), (5282352899/10000000000 : ℝ)] ![(13884971802849/100000000000000 : ℝ), (8611502790263/20000000000000 : ℝ), (5382189278891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-560403227/2500000000 : ℝ)|^4221 ≤ (13884971802849/100000000000000 : ℝ)^3197
        have hw : |(-560403227/2500000000 : ℝ)|=(560403227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282352873/10000000000 : ℝ)|^4221 ≤ (8611502790263/20000000000000 : ℝ)^3197
        have hw : |(5282352873/10000000000 : ℝ)|=(5282352873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282352899/10000000000 : ℝ)|^4221 ≤ (5382189278891/12500000000000 : ℝ)^3197
        have hw : |(5282352899/10000000000 : ℝ)|=(5282352899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340489311/2500000000 : ℝ)*x 0 + (-2135797459/10000000000 : ℝ)*x 1 + (42258823/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340489311/2500000000 : ℝ)^4221 ≤ (21958139644037/50000000000000 : ℝ)^3197 := by
    have hnat : (1340489311 : ℕ)^4221*50000000000000^3197 ≤ 21958139644037^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340489311 2500000000 21958139644037 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135797459/10000000000 : ℝ)^4221 ≤ (13026206713247/100000000000000 : ℝ)^3197 := by
    have hnat : (2135797459 : ℕ)^4221*100000000000000^3197 ≤ 13026206713247^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135797459 10000000000 13026206713247 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42258823/80000000 : ℝ)^4221 ≤ (43057513972839/100000000000000 : ℝ)^3197 := by
    have hnat : (42258823 : ℕ)^4221*100000000000000^3197 ≤ 43057513972839^3197*80000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42258823 80000000 43057513972839 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340489311/2500000000 : ℝ), (-2135797459/10000000000 : ℝ), (42258823/80000000 : ℝ)] ![(21958139644037/50000000000000 : ℝ), (13026206713247/100000000000000 : ℝ), (43057513972839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340489311/2500000000 : ℝ)|^4221 ≤ (21958139644037/50000000000000 : ℝ)^3197
        have hw : |(1340489311/2500000000 : ℝ)|=(1340489311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135797459/10000000000 : ℝ)|^4221 ≤ (13026206713247/100000000000000 : ℝ)^3197
        have hw : |(-2135797459/10000000000 : ℝ)|=(2135797459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42258823/80000000 : ℝ)|^4221 ≤ (43057513972839/100000000000000 : ℝ)^3197
        have hw : |(42258823/80000000 : ℝ)|=(42258823/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134048931/250000000 : ℝ)*x 0 + (5282352881/10000000000 : ℝ)*x 1 + (-2135797457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134048931/250000000 : ℝ)^4221 ≤ (43916279244819/100000000000000 : ℝ)^3197 := by
    have hnat : (134048931 : ℕ)^4221*100000000000000^3197 ≤ 43916279244819^3197*250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134048931 250000000 43916279244819 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282352881/10000000000 : ℝ)^4221 ≤ (43057514037411/100000000000000 : ℝ)^3197 := by
    have hnat : (5282352881 : ℕ)^4221*100000000000000^3197 ≤ 43057514037411^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282352881 10000000000 43057514037411 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135797457/10000000000 : ℝ)^4221 ≤ (6513103348571/50000000000000 : ℝ)^3197 := by
    have hnat : (2135797457 : ℕ)^4221*50000000000000^3197 ≤ 6513103348571^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135797457 10000000000 6513103348571 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134048931/250000000 : ℝ), (5282352881/10000000000 : ℝ), (-2135797457/10000000000 : ℝ)] ![(43916279244819/100000000000000 : ℝ), (43057514037411/100000000000000 : ℝ), (6513103348571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134048931/250000000 : ℝ)|^4221 ≤ (43916279244819/100000000000000 : ℝ)^3197
        have hw : |(134048931/250000000 : ℝ)|=(134048931/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282352881/10000000000 : ℝ)|^4221 ≤ (43057514037411/100000000000000 : ℝ)^3197
        have hw : |(5282352881/10000000000 : ℝ)|=(5282352881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135797457/10000000000 : ℝ)|^4221 ≤ (6513103348571/50000000000000 : ℝ)^3197
        have hw : |(-2135797457/10000000000 : ℝ)|=(2135797457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242943757/10000000000 : ℝ)*x 0 + (88105389/200000000 : ℝ)*x 1 + (4405269377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242943757/10000000000 : ℝ)^4221 ≤ (32241036725293/100000000000000 : ℝ)^3197 := by
    have hnat : (4242943757 : ℕ)^4221*100000000000000^3197 ≤ 32241036725293^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242943757 10000000000 32241036725293 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88105389/200000000 : ℝ)^4221 ≤ (4234935250483/12500000000000 : ℝ)^3197 := by
    have hnat : (88105389 : ℕ)^4221*12500000000000^3197 ≤ 4234935250483^3197*200000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88105389 200000000 4234935250483 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405269377/10000000000 : ℝ)^4221 ≤ (16939740631311/50000000000000 : ℝ)^3197 := by
    have hnat : (4405269377 : ℕ)^4221*50000000000000^3197 ≤ 16939740631311^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405269377 10000000000 16939740631311 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242943757/10000000000 : ℝ), (88105389/200000000 : ℝ), (4405269377/10000000000 : ℝ)] ![(32241036725293/100000000000000 : ℝ), (4234935250483/12500000000000 : ℝ), (16939740631311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242943757/10000000000 : ℝ)|^4221 ≤ (32241036725293/100000000000000 : ℝ)^3197
        have hw : |(4242943757/10000000000 : ℝ)|=(4242943757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88105389/200000000 : ℝ)|^4221 ≤ (4234935250483/12500000000000 : ℝ)^3197
        have hw : |(88105389/200000000 : ℝ)|=(88105389/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405269377/10000000000 : ℝ)|^4221 ≤ (16939740631311/50000000000000 : ℝ)^3197
        have hw : |(4405269377/10000000000 : ℝ)|=(4405269377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_8 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437912757/2000000000 : ℝ)*x 0 + (1304830563/2500000000 : ℝ)*x 1 + (538435353/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437912757/2000000000 : ℝ)^4221 ≤ (1346089557961/10000000000000 : ℝ)^3197 := by
    have hnat : (437912757 : ℕ)^4221*10000000000000^3197 ≤ 1346089557961^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437912757 2000000000 1346089557961 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304830563/2500000000 : ℝ)^4221 ≤ (8476095244599/20000000000000 : ℝ)^3197 := by
    have hnat : (1304830563 : ℕ)^4221*20000000000000^3197 ≤ 8476095244599^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304830563 2500000000 8476095244599 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538435353/1000000000 : ℝ)^4221 ≤ (44158628188251/100000000000000 : ℝ)^3197 := by
    have hnat : (538435353 : ℕ)^4221*100000000000000^3197 ≤ 44158628188251^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538435353 1000000000 44158628188251 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437912757/2000000000 : ℝ), (1304830563/2500000000 : ℝ), (538435353/1000000000 : ℝ)] ![(1346089557961/10000000000000 : ℝ), (8476095244599/20000000000000 : ℝ), (44158628188251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437912757/2000000000 : ℝ)|^4221 ≤ (1346089557961/10000000000000 : ℝ)^3197
        have hw : |(-437912757/2000000000 : ℝ)|=(437912757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304830563/2500000000 : ℝ)|^4221 ≤ (8476095244599/20000000000000 : ℝ)^3197
        have hw : |(1304830563/2500000000 : ℝ)|=(1304830563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538435353/1000000000 : ℝ)|^4221 ≤ (44158628188251/100000000000000 : ℝ)^3197
        have hw : |(538435353/1000000000 : ℝ)|=(538435353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_9 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322515527/2500000000 : ℝ)*x 0 + (-1047636139/5000000000 : ℝ)*x 1 + (5384353319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322515527/2500000000 : ℝ)^4221 ≤ (5392562545779/12500000000000 : ℝ)^3197 := by
    have hnat : (1322515527 : ℕ)^4221*12500000000000^3197 ≤ 5392562545779^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322515527 2500000000 5392562545779 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047636139/5000000000 : ℝ)^4221 ≤ (254017474089/2000000000000 : ℝ)^3197 := by
    have hnat : (1047636139 : ℕ)^4221*2000000000000^3197 ≤ 254017474089^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047636139 5000000000 254017474089 2000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384353319/10000000000 : ℝ)^4221 ≤ (44158625903509/100000000000000 : ℝ)^3197 := by
    have hnat : (5384353319 : ℕ)^4221*100000000000000^3197 ≤ 44158625903509^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384353319 10000000000 44158625903509 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322515527/2500000000 : ℝ), (-1047636139/5000000000 : ℝ), (5384353319/10000000000 : ℝ)] ![(5392562545779/12500000000000 : ℝ), (254017474089/2000000000000 : ℝ), (44158625903509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322515527/2500000000 : ℝ)|^4221 ≤ (5392562545779/12500000000000 : ℝ)^3197
        have hw : |(1322515527/2500000000 : ℝ)|=(1322515527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047636139/5000000000 : ℝ)|^4221 ≤ (254017474089/2000000000000 : ℝ)^3197
        have hw : |(-1047636139/5000000000 : ℝ)|=(1047636139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384353319/10000000000 : ℝ)|^4221 ≤ (44158625903509/100000000000000 : ℝ)^3197
        have hw : |(5384353319/10000000000 : ℝ)|=(5384353319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_10 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058012393/2000000000 : ℝ)*x 0 + (2692176827/5000000000 : ℝ)*x 1 + (-2095272019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058012393/2000000000 : ℝ)^4221 ≤ (21570249413271/50000000000000 : ℝ)^3197 := by
    have hnat : (1058012393 : ℕ)^4221*50000000000000^3197 ≤ 21570249413271^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058012393 2000000000 21570249413271 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692176827/5000000000 : ℝ)^4221 ≤ (44158629530943/100000000000000 : ℝ)^3197 := by
    have hnat : (2692176827 : ℕ)^4221*100000000000000^3197 ≤ 44158629530943^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692176827 5000000000 44158629530943 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095272019/10000000000 : ℝ)^4221 ≤ (12700871631611/100000000000000 : ℝ)^3197 := by
    have hnat : (2095272019 : ℕ)^4221*100000000000000^3197 ≤ 12700871631611^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095272019 10000000000 12700871631611 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058012393/2000000000 : ℝ), (2692176827/5000000000 : ℝ), (-2095272019/10000000000 : ℝ)] ![(21570249413271/50000000000000 : ℝ), (44158629530943/100000000000000 : ℝ), (12700871631611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058012393/2000000000 : ℝ)|^4221 ≤ (21570249413271/50000000000000 : ℝ)^3197
        have hw : |(1058012393/2000000000 : ℝ)|=(1058012393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692176827/5000000000 : ℝ)|^4221 ≤ (44158629530943/100000000000000 : ℝ)^3197
        have hw : |(2692176827/5000000000 : ℝ)|=(2692176827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095272019/10000000000 : ℝ)|^4221 ≤ (12700871631611/100000000000000 : ℝ)^3197
        have hw : |(-2095272019/10000000000 : ℝ)|=(2095272019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_11 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1119552651/2500000000 : ℝ)*x 0 + (535939429/1250000000 : ℝ)*x 1 + (4287515543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119552651/2500000000 : ℝ)^4221 ≤ (34622082873831/100000000000000 : ℝ)^3197 := by
    have hnat : (1119552651 : ℕ)^4221*100000000000000^3197 ≤ 34622082873831^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119552651 2500000000 34622082873831 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535939429/1250000000 : ℝ)^4221 ≤ (6537791600289/20000000000000 : ℝ)^3197 := by
    have hnat : (535939429 : ℕ)^4221*20000000000000^3197 ≤ 6537791600289^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535939429 1250000000 6537791600289 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4287515543/10000000000 : ℝ)^4221 ≤ (32688959118799/100000000000000 : ℝ)^3197 := by
    have hnat : (4287515543 : ℕ)^4221*100000000000000^3197 ≤ 32688959118799^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287515543 10000000000 32688959118799 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119552651/2500000000 : ℝ), (535939429/1250000000 : ℝ), (4287515543/10000000000 : ℝ)] ![(34622082873831/100000000000000 : ℝ), (6537791600289/20000000000000 : ℝ), (32688959118799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119552651/2500000000 : ℝ)|^4221 ≤ (34622082873831/100000000000000 : ℝ)^3197
        have hw : |(1119552651/2500000000 : ℝ)|=(1119552651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(535939429/1250000000 : ℝ)|^4221 ≤ (6537791600289/20000000000000 : ℝ)^3197
        have hw : |(535939429/1250000000 : ℝ)|=(535939429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4287515543/10000000000 : ℝ)|^4221 ≤ (32688959118799/100000000000000 : ℝ)^3197
        have hw : |(4287515543/10000000000 : ℝ)|=(4287515543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_12 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51139133/250000000 : ℝ)*x 0 + (5436565307/10000000000 : ℝ)*x 1 + (5274271341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51139133/250000000 : ℝ)^4221 ≤ (96129504821/781250000000 : ℝ)^3197 := by
    have hnat : (51139133 : ℕ)^4221*781250000000^3197 ≤ 96129504821^3197*250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51139133 250000000 96129504821 781250000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436565307/10000000000 : ℝ)^4221 ≤ (11181215449689/25000000000000 : ℝ)^3197 := by
    have hnat : (5436565307 : ℕ)^4221*25000000000000^3197 ≤ 11181215449689^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436565307 10000000000 11181215449689 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274271341/10000000000 : ℝ)^4221 ≤ (21485280783501/50000000000000 : ℝ)^3197 := by
    have hnat : (5274271341 : ℕ)^4221*50000000000000^3197 ≤ 21485280783501^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274271341 10000000000 21485280783501 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51139133/250000000 : ℝ), (5436565307/10000000000 : ℝ), (5274271341/10000000000 : ℝ)] ![(96129504821/781250000000 : ℝ), (11181215449689/25000000000000 : ℝ), (21485280783501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51139133/250000000 : ℝ)|^4221 ≤ (96129504821/781250000000 : ℝ)^3197
        have hw : |(-51139133/250000000 : ℝ)|=(51139133/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436565307/10000000000 : ℝ)|^4221 ≤ (11181215449689/25000000000000 : ℝ)^3197
        have hw : |(5436565307/10000000000 : ℝ)|=(5436565307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274271341/10000000000 : ℝ)|^4221 ≤ (21485280783501/50000000000000 : ℝ)^3197
        have hw : |(5274271341/10000000000 : ℝ)|=(5274271341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_13 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367652851/10000000000 : ℝ)*x 0 + (-267368401/1250000000 : ℝ)*x 1 + (2637134831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367652851/10000000000 : ℝ)^4221 ≤ (5497235054033/12500000000000 : ℝ)^3197 := by
    have hnat : (5367652851 : ℕ)^4221*12500000000000^3197 ≤ 5497235054033^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367652851 10000000000 5497235054033 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267368401/1250000000 : ℝ)^4221 ≤ (13051576048531/100000000000000 : ℝ)^3197 := by
    have hnat : (267368401 : ℕ)^4221*100000000000000^3197 ≤ 13051576048531^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267368401 1250000000 13051576048531 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637134831/5000000000 : ℝ)^4221 ≤ (42970543506411/100000000000000 : ℝ)^3197 := by
    have hnat : (2637134831 : ℕ)^4221*100000000000000^3197 ≤ 42970543506411^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637134831 5000000000 42970543506411 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367652851/10000000000 : ℝ), (-267368401/1250000000 : ℝ), (2637134831/5000000000 : ℝ)] ![(5497235054033/12500000000000 : ℝ), (13051576048531/100000000000000 : ℝ), (42970543506411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367652851/10000000000 : ℝ)|^4221 ≤ (5497235054033/12500000000000 : ℝ)^3197
        have hw : |(5367652851/10000000000 : ℝ)|=(5367652851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267368401/1250000000 : ℝ)|^4221 ≤ (13051576048531/100000000000000 : ℝ)^3197
        have hw : |(-267368401/1250000000 : ℝ)|=(267368401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637134831/5000000000 : ℝ)|^4221 ≤ (42970543506411/100000000000000 : ℝ)^3197
        have hw : |(2637134831/5000000000 : ℝ)|=(2637134831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_14 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367652401/10000000000 : ℝ)*x 0 + (329641863/625000000 : ℝ)*x 1 + (-2138947617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367652401/10000000000 : ℝ)^4221 ≤ (21988937782219/50000000000000 : ℝ)^3197 := by
    have hnat : (5367652401 : ℕ)^4221*50000000000000^3197 ≤ 21988937782219^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367652401 10000000000 21988937782219 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329641863/625000000 : ℝ)^4221 ≤ (42970545076897/100000000000000 : ℝ)^3197 := by
    have hnat : (329641863 : ℕ)^4221*100000000000000^3197 ≤ 42970545076897^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329641863 625000000 42970545076897 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138947617/10000000000 : ℝ)^4221 ≤ (6525789671779/50000000000000 : ℝ)^3197 := by
    have hnat : (2138947617 : ℕ)^4221*50000000000000^3197 ≤ 6525789671779^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138947617 10000000000 6525789671779 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367652401/10000000000 : ℝ), (329641863/625000000 : ℝ), (-2138947617/10000000000 : ℝ)] ![(21988937782219/50000000000000 : ℝ), (42970545076897/100000000000000 : ℝ), (6525789671779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367652401/10000000000 : ℝ)|^4221 ≤ (21988937782219/50000000000000 : ℝ)^3197
        have hw : |(5367652401/10000000000 : ℝ)|=(5367652401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329641863/625000000 : ℝ)|^4221 ≤ (42970545076897/100000000000000 : ℝ)^3197
        have hw : |(329641863/625000000 : ℝ)|=(329641863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138947617/10000000000 : ℝ)|^4221 ≤ (6525789671779/50000000000000 : ℝ)^3197
        have hw : |(-2138947617/10000000000 : ℝ)|=(2138947617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_box_15 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224047543/10000000000 : ℝ)*x 0 + (4414594407/10000000000 : ℝ)*x 1 + (441459511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224047543/10000000000 : ℝ)^4221 ≤ (16025796754487/50000000000000 : ℝ)^3197 := by
    have hnat : (4224047543 : ℕ)^4221*50000000000000^3197 ≤ 16025796754487^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224047543 10000000000 16025796754487 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414594407/10000000000 : ℝ)^4221 ≤ (8493549916443/25000000000000 : ℝ)^3197 := by
    have hnat : (4414594407 : ℕ)^4221*25000000000000^3197 ≤ 8493549916443^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414594407 10000000000 8493549916443 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441459511/1000000000 : ℝ)^4221 ≤ (33974206808867/100000000000000 : ℝ)^3197 := by
    have hnat : (441459511 : ℕ)^4221*100000000000000^3197 ≤ 33974206808867^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441459511 1000000000 33974206808867 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224047543/10000000000 : ℝ), (4414594407/10000000000 : ℝ), (441459511/1000000000 : ℝ)] ![(16025796754487/50000000000000 : ℝ), (8493549916443/25000000000000 : ℝ), (33974206808867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224047543/10000000000 : ℝ)|^4221 ≤ (16025796754487/50000000000000 : ℝ)^3197
        have hw : |(4224047543/10000000000 : ℝ)|=(4224047543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414594407/10000000000 : ℝ)|^4221 ≤ (8493549916443/25000000000000 : ℝ)^3197
        have hw : |(4414594407/10000000000 : ℝ)|=(4414594407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441459511/1000000000 : ℝ)|^4221 ≤ (33974206808867/100000000000000 : ℝ)^3197
        have hw : |(441459511/1000000000 : ℝ)|=(441459511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7781/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59383/100000 : ℝ) ∧ (80129/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83361/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11487/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (13383339539990099/100000000000000000000 : ℝ) := by
    have hpowers : (11487/100000 : ℝ)^8441 ≤ (13383339539990099/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11487 : ℕ)^8441*100000000000000000000^2048 ≤ 13383339539990099^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11487 100000 13383339539990099 100000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11487/100000 : ℝ)) (X := (13383339539990099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (8441/2048 : ℝ) ≤ (31221379330710673/100000000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^8441 ≤ (31221379330710673/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3527 : ℕ)^8441*100000000000000000000^2048 ≤ 31221379330710673^2048*25000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 31221379330710673 100000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (31221379330710673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013383339539990099/50000000000000000000 : ℝ) ≤ (2500162340371837/2500000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50013383339539990099/50000000000000000000 : ℝ)^2048 ≤ (2500162340371837/2500000000000000 : ℝ)^8441 := by
      have hnat : (50013383339539990099 : ℕ)^2048*2500000000000000^8441 ≤ 2500162340371837^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013383339539990099 50000000000000000000 2500162340371837 2500000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162340371837/2500000000000000 : ℝ)) (X := (50013383339539990099/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011151179717675193/25000000000000000000 : ℝ) ≤ (10001082040493409/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (25011151179717675193/25000000000000000000 : ℝ)^2048 ≤ (10001082040493409/10000000000000000 : ℝ)^8441 := by
      have hnat : (25011151179717675193 : ℕ)^2048*10000000000000000^8441 ≤ 10001082040493409^8441*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011151179717675193 25000000000000000000 10001082040493409 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001082040493409/10000000000000000 : ℝ)) (X := (25011151179717675193/25000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031221379330710673/50000000000000000000 : ℝ) ≤ (1000151471949947/1000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50031221379330710673/50000000000000000000 : ℝ)^2048 ≤ (1000151471949947/1000000000000000 : ℝ)^8441 := by
      have hnat : (50031221379330710673 : ℕ)^2048*1000000000000000^8441 ≤ 1000151471949947^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031221379330710673 50000000000000000000 1000151471949947 1000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000151471949947/1000000000000000 : ℝ)) (X := (50031221379330710673/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13383339539990099/100000000000000000000 : ℝ) ≤ ((13100880804486546847/13105000000000000000 : ℝ)+2*(432679006061/262100000000000 : ℝ)*(11487/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (13100880804486546847/13105000000000000000 : ℝ)+2*(432679006061/262100000000000 : ℝ)*(11487/100000 : ℝ)=(2500162340371837/2500000000000000 : ℝ) by norm_num, show 1+2*(13383339539990099/100000000000000000000 : ℝ)=(50013383339539990099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31221379330710673/100000000000000000000 : ℝ)+(13383339539990099/100000000000000000000 : ℝ) ≤ ((13100880804486546847/13105000000000000000 : ℝ)+(432679006061/262100000000000 : ℝ)*((3527/25000 : ℝ)+(11487/100000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (13100880804486546847/13105000000000000000 : ℝ)+(432679006061/262100000000000 : ℝ)*((3527/25000 : ℝ)+(11487/100000 : ℝ))=(10001082040493409/10000000000000000 : ℝ) by norm_num, show 1+(31221379330710673/100000000000000000000 : ℝ)+(13383339539990099/100000000000000000000 : ℝ)=(25011151179717675193/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31221379330710673/100000000000000000000 : ℝ) ≤ ((13100880804486546847/13105000000000000000 : ℝ)+2*(432679006061/262100000000000 : ℝ)*(3527/25000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (13100880804486546847/13105000000000000000 : ℝ)+2*(432679006061/262100000000000 : ℝ)*(3527/25000 : ℝ)=(1000151471949947/1000000000000000 : ℝ) by norm_num, show 1+2*(31221379330710673/100000000000000000000 : ℝ)=(50031221379330710673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13100880804486546847/13105000000000000000 : ℝ)*(X 1 0+X 2 0)+(432679006061/262100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (13100880804486546847/13105000000000000000 : ℝ)) (alpha := (432679006061/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13100880804486546847/13105000000000000000 : ℝ)*(X 0 1+X 2 1)+(432679006061/262100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (13100880804486546847/13105000000000000000 : ℝ)) (alpha := (432679006061/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13100880804486546847/13105000000000000000 : ℝ)*(X 0 2+X 1 2)+(432679006061/262100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (11487/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (13100880804486546847/13105000000000000000 : ℝ)) (alpha := (432679006061/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-9966303/50000000 : ℝ)*X 0 0+(2687369793/5000000000 : ℝ)*X 0 1+(5374739539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296840891/10000000000 : ℝ)*X 1 0+(-524788189/2500000000 : ℝ)*X 1 1+(1343684923/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529684089/1000000000 : ℝ)*X 2 0+(2687369907/5000000000 : ℝ)*X 2 1+(-131197037/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228141413/5000000000 : ℝ)*X 0 0+(4298619689/10000000000 : ℝ)*X 0 1+(171944807/400000000 : ℝ)*X 0 2+(2228141413/5000000000 : ℝ)*X 1 0+(4298619689/10000000000 : ℝ)*X 1 1+(171944807/400000000 : ℝ)*X 1 2+(2228141413/5000000000 : ℝ)*X 2 0+(4298619689/10000000000 : ℝ)*X 2 1+(171944807/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-560403227/2500000000 : ℝ)*X 0 0+(5282352873/10000000000 : ℝ)*X 0 1+(5282352899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340489311/2500000000 : ℝ)*X 1 0+(-2135797459/10000000000 : ℝ)*X 1 1+(42258823/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134048931/250000000 : ℝ)*X 2 0+(5282352881/10000000000 : ℝ)*X 2 1+(-2135797457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242943757/10000000000 : ℝ)*X 0 0+(88105389/200000000 : ℝ)*X 0 1+(4405269377/10000000000 : ℝ)*X 0 2+(4242943757/10000000000 : ℝ)*X 1 0+(88105389/200000000 : ℝ)*X 1 1+(4405269377/10000000000 : ℝ)*X 1 2+(4242943757/10000000000 : ℝ)*X 2 0+(88105389/200000000 : ℝ)*X 2 1+(4405269377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-437912757/2000000000 : ℝ)*X 0 0+(1304830563/2500000000 : ℝ)*X 0 1+(538435353/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322515527/2500000000 : ℝ)*X 1 0+(-1047636139/5000000000 : ℝ)*X 1 1+(5384353319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1058012393/2000000000 : ℝ)*X 2 0+(2692176827/5000000000 : ℝ)*X 2 1+(-2095272019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1119552651/2500000000 : ℝ)*X 0 0+(535939429/1250000000 : ℝ)*X 0 1+(4287515543/10000000000 : ℝ)*X 0 2+(1119552651/2500000000 : ℝ)*X 1 0+(535939429/1250000000 : ℝ)*X 1 1+(4287515543/10000000000 : ℝ)*X 1 2+(1119552651/2500000000 : ℝ)*X 2 0+(535939429/1250000000 : ℝ)*X 2 1+(4287515543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-51139133/250000000 : ℝ)*X 0 0+(5436565307/10000000000 : ℝ)*X 0 1+(5274271341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367652851/10000000000 : ℝ)*X 1 0+(-267368401/1250000000 : ℝ)*X 1 1+(2637134831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367652401/10000000000 : ℝ)*X 2 0+(329641863/625000000 : ℝ)*X 2 1+(-2138947617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4224047543/10000000000 : ℝ)*X 0 0+(4414594407/10000000000 : ℝ)*X 0 1+(441459511/1000000000 : ℝ)*X 0 2+(4224047543/10000000000 : ℝ)*X 1 0+(4414594407/10000000000 : ℝ)*X 1 1+(441459511/1000000000 : ℝ)*X 1 2+(4224047543/10000000000 : ℝ)*X 2 0+(4414594407/10000000000 : ℝ)*X 2 1+(441459511/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7781/12500 : ℝ) ≤ (-10196610905098320895863769583823/16381250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1974851/12500000000000 : ℝ)*(lower0) + (4945111/12500000000000 : ℝ)*(lower2) + (18587659/50000000000000 : ℝ)*(lower4) + (1246503/25000000000000 : ℝ)*(lower5) + (100215223662953/2500000000000 : ℝ)*(major0) + (100215223662953/2500000000000 : ℝ)*(major1) + (100215223662953/2500000000000 : ℝ)*(major2) + (1401022157/100000000000000 : ℝ)*(sp1) + (351687537/50000000000000 : ℝ)*(sp2) + (2696582893792543/50000000000000 : ℝ)*(sp4) + (5393164386562929/100000000000000 : ℝ)*(sp5) + (1348291271052503/25000000000000 : ℝ)*(sp6) + (661199877236451/25000000000000 : ℝ)*(sp7) + (568536369/50000000000000 : ℝ)*(sp15) + (2644800646018543/100000000000000 : ℝ)*(f.failure) + (2696582893792543/50000000000000 : ℝ)*(f.sum) + (488138854891/262100000000000000000000000 : ℝ)*base65 + (540114028535459191/32762500000000000000000000000000 : ℝ)*base67 + (755963097268984191/32762500000000000000000000000000 : ℝ)*base69 + (2213523042038303309/32762500000000000000000000000000 : ℝ)*base72 + (38849512407941/2621000000000000000000000000 : ℝ)*base73 + (797582539277671691/32762500000000000000000000000000 : ℝ)*base75 + (1957607348500234191/32762500000000000000000000000000 : ℝ)*base77 + (512747854731165809/32762500000000000000000000000000 : ℝ)*base80 + (2782669067887/655250000000000000000000000 : ℝ)*base81 + (16393109/10000000000000000000000 : ℝ)*base90 + (16393109/10000000000000000000000 : ℝ)*base92 + (16393109/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59383/100000 : ℝ) ≤ (389122709111752283188165194994149/655250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35561053/100000000000000 : ℝ)*(upper0) + (14565549/20000000000000 : ℝ)*(lower1) + (8699649/20000000000000 : ℝ)*(upper4) + (1083861/1250000000000 : ℝ)*(upper5) + (4074529038746089/100000000000000 : ℝ)*(major0) + (4074529038746089/100000000000000 : ℝ)*(major1) + (4074529038746089/100000000000000 : ℝ)*(major2) + (5440969535570873/100000000000000 : ℝ)*(sp0) + (5440968407802993/100000000000000 : ℝ)*(sp1) + (1360240411041221/25000000000000 : ℝ)*(sp2) + (2688293347932729/100000000000000 : ℝ)*(sp3) + (28194197/2500000000000 : ℝ)*(sp5) + (1972851497/25000000000000 : ℝ)*(sp6) + (2093219/3125000000000 : ℝ)*(sp7) + (336036676864467/12500000000000 : ℝ)*(f.failure) + (5440969535570873/100000000000000 : ℝ)*(f.sum) + (70458841172621/13105000000000000000000000000 : ℝ)*base66 + (21118091035311518617/1310500000000000000000000000000000 : ℝ)*base68 + (2361199567358981383/1310500000000000000000000000000000 : ℝ)*base69 + (14204964020468518617/1310500000000000000000000000000000 : ℝ)*base72 + (3769233270321/819062500000000000000000000 : ℝ)*base74 + (3135437933235518617/1310500000000000000000000000000000 : ℝ)*base76 + (11712590115737018617/1310500000000000000000000000000000 : ℝ)*base78 + (1886079434415481383/1310500000000000000000000000000000 : ℝ)*base79 + (30569363424503/6552500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8979521/1250000000000000000000 : ℝ)*base90 + (8979521/1250000000000000000000 : ℝ)*base92 + (8979521/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80129/100000 : ℝ) ≤ (65633004968120470336795195069773/81906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33962547/20000000000000 : ℝ)*(lower3) + (46909923/100000000000000 : ℝ)*(upper4) + (7008391/12500000000000 : ℝ)*(lower5) + (1135295454843403/25000000000000 : ℝ)*(major0) + (1135295454843403/25000000000000 : ℝ)*(major1) + (1135295454843403/25000000000000 : ℝ)*(major2) + (787942667/10000000000000 : ℝ)*(sp0) + (51523908121/100000000000000 : ℝ)*(sp1) + (248545753421/100000000000000 : ℝ)*(sp2) + (5248975201/5000000000000 : ℝ)*(sp3) + (1514865869367211/25000000000000 : ℝ)*(sp8) + (6059419832987393/100000000000000 : ℝ)*(sp9) + (3029611405571047/50000000000000 : ℝ)*(sp10) + (2996076680969331/100000000000000 : ℝ)*(sp11) + (374522707559169/12500000000000 : ℝ)*(f.failure) + (3029735678447757/50000000000000 : ℝ)*(f.sum) + (248734267603/3276250000000000000000000000 : ℝ)*base65 + (651278989947449659/327625000000000000000000000000000 : ℝ)*base68 + (878879619755324659/327625000000000000000000000000000 : ℝ)*base70 + (892504565872324659/327625000000000000000000000000000 : ℝ)*base72 + (4265069948461/6552500000000000000000000000 : ℝ)*base73 + (258627287491050341/327625000000000000000000000000000 : ℝ)*base75 + (990549343252949659/327625000000000000000000000000000 : ℝ)*base78 + (1260150349735199659/327625000000000000000000000000000 : ℝ)*base80 + (101384474994757/13105000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14675653/1250000000000000000000 : ℝ)*base89 + (14675653/1250000000000000000000 : ℝ)*base91 + (14675653/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83361/100000 : ℝ) ≤ (-34137976427960792719950176218221/40953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4572639/20000000000000 : ℝ)*(lower3) + (19660273/5000000000000 : ℝ)*(lower4) + (1572093/100000000000000 : ℝ)*(upper5) + (286050495132769/6250000000000 : ℝ)*(major0) + (286050495132769/6250000000000 : ℝ)*(major1) + (286050495132769/6250000000000 : ℝ)*(major2) + (42298510301/100000000000000 : ℝ)*(sp4) + (258776439789/20000000000000 : ℝ)*(sp5) + (1497539289551/100000000000000 : ℝ)*(sp6) + (55397183951/10000000000000 : ℝ)*(sp7) + (3080836354854363/50000000000000 : ℝ)*(sp12) + (3080210563010041/50000000000000 : ℝ)*(sp13) + (1540054367232369/25000000000000 : ℝ)*(sp14) + (1509566542176361/50000000000000 : ℝ)*(sp15) + (377460882024029/12500000000000 : ℝ)*(f.failure) + (6161715008219027/100000000000000 : ℝ)*(f.sum) + (296945867607/102382812500000000000000000 : ℝ)*base66 + (577707135519626907/81906250000000000000000000000000 : ℝ)*base68 + (26535394781064407/81906250000000000000000000000000 : ℝ)*base70 + (51807864964908157/81906250000000000000000000000000 : ℝ)*base72 + (39536751575529/13105000000000000000000000000 : ℝ)*base73 + (147930242116623093/81906250000000000000000000000000 : ℝ)*base75 + (114510167371529343/81906250000000000000000000000000 : ℝ)*base77 + (562300028002876907/81906250000000000000000000000000 : ℝ)*base80 + (40682369216511/13105000000000000000000000000 : ℝ)*base82 + (4691473/1250000000000000000000 : ℝ)*base89 + (4691473/1250000000000000000000 : ℝ)*base91 + (4691473/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1249_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59383/100000 : ℝ) else (80129/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83361/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1249_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1249_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59383/100000 : ℝ) else (80129/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83361/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1249_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1249_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1249_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59383/100000 : ℝ) else (80129/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83361/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
