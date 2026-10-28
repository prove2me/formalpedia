-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:57.662257+00:00
-- url     : https://prove2.me/submissions/c0f22d82-8196-4833-91ae-ccf5aaacfeed

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
theorem support_rectangle_w1120_s0_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898793251/10000000000 : ℝ)*x 0 + (6059428881/10000000000 : ℝ)*x 1 + (1194420923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898793251/10000000000 : ℝ)^8313 ≤ (11031010934209/100000000000000 : ℝ)^6265 := by
    have hnat : (1898793251 : ℕ)^8313*100000000000000^6265 ≤ 11031010934209^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898793251 10000000000 11031010934209 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6059428881/10000000000 : ℝ)^8313 ≤ (1286025592309/2500000000000 : ℝ)^6265 := by
    have hnat : (6059428881 : ℕ)^8313*2500000000000^6265 ≤ 1286025592309^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059428881 10000000000 1286025592309 2500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194420923/2500000000 : ℝ)^8313 ≤ (3752796535919/10000000000000 : ℝ)^6265 := by
    have hnat : (1194420923 : ℕ)^8313*10000000000000^6265 ≤ 3752796535919^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194420923 2500000000 3752796535919 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898793251/10000000000 : ℝ), (6059428881/10000000000 : ℝ), (1194420923/2500000000 : ℝ)] ![(11031010934209/100000000000000 : ℝ), (1286025592309/2500000000000 : ℝ), (3752796535919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898793251/10000000000 : ℝ)|^8313 ≤ (11031010934209/100000000000000 : ℝ)^6265
        have hw : |(-1898793251/10000000000 : ℝ)|=(1898793251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6059428881/10000000000 : ℝ)|^8313 ≤ (1286025592309/2500000000000 : ℝ)^6265
        have hw : |(6059428881/10000000000 : ℝ)|=(6059428881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194420923/2500000000 : ℝ)|^8313 ≤ (3752796535919/10000000000000 : ℝ)^6265
        have hw : |(1194420923/2500000000 : ℝ)|=(1194420923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518032801/10000000000 : ℝ)*x 0 + (-1317499291/5000000000 : ℝ)*x 1 + (4777683727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518032801/10000000000 : ℝ)^8313 ≤ (11358336776777/25000000000000 : ℝ)^6265 := by
    have hnat : (5518032801 : ℕ)^8313*25000000000000^6265 ≤ 11358336776777^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518032801 10000000000 11358336776777 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317499291/5000000000 : ℝ)^8313 ≤ (17038687151693/100000000000000 : ℝ)^6265 := by
    have hnat : (1317499291 : ℕ)^8313*100000000000000^6265 ≤ 17038687151693^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317499291 5000000000 17038687151693 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4777683727/10000000000 : ℝ)^8313 ≤ (37527965723979/100000000000000 : ℝ)^6265 := by
    have hnat : (4777683727 : ℕ)^8313*100000000000000^6265 ≤ 37527965723979^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777683727 10000000000 37527965723979 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518032801/10000000000 : ℝ), (-1317499291/5000000000 : ℝ), (4777683727/10000000000 : ℝ)] ![(11358336776777/25000000000000 : ℝ), (17038687151693/100000000000000 : ℝ), (37527965723979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518032801/10000000000 : ℝ)|^8313 ≤ (11358336776777/25000000000000 : ℝ)^6265
        have hw : |(5518032801/10000000000 : ℝ)|=(5518032801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317499291/5000000000 : ℝ)|^8313 ≤ (17038687151693/100000000000000 : ℝ)^6265
        have hw : |(-1317499291/5000000000 : ℝ)|=(1317499291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4777683727/10000000000 : ℝ)|^8313 ≤ (37527965723979/100000000000000 : ℝ)^6265
        have hw : |(4777683727/10000000000 : ℝ)|=(4777683727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518032951/10000000000 : ℝ)*x 0 + (2388841793/5000000000 : ℝ)*x 1 + (-2634998563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518032951/10000000000 : ℝ)^8313 ≤ (1135833718647/2500000000000 : ℝ)^6265 := by
    have hnat : (5518032951 : ℕ)^8313*2500000000000^6265 ≤ 1135833718647^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518032951 10000000000 1135833718647 2500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2388841793/5000000000 : ℝ)^8313 ≤ (37527964254399/100000000000000 : ℝ)^6265 := by
    have hnat : (2388841793 : ℕ)^8313*100000000000000^6265 ≤ 37527964254399^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388841793 5000000000 37527964254399 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2634998563/10000000000 : ℝ)^8313 ≤ (17038686988671/100000000000000 : ℝ)^6265 := by
    have hnat : (2634998563 : ℕ)^8313*100000000000000^6265 ≤ 17038686988671^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634998563 10000000000 17038686988671 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518032951/10000000000 : ℝ), (2388841793/5000000000 : ℝ), (-2634998563/10000000000 : ℝ)] ![(1135833718647/2500000000000 : ℝ), (37527964254399/100000000000000 : ℝ), (17038686988671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518032951/10000000000 : ℝ)|^8313 ≤ (1135833718647/2500000000000 : ℝ)^6265
        have hw : |(5518032951/10000000000 : ℝ)|=(5518032951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2388841793/5000000000 : ℝ)|^8313 ≤ (37527964254399/100000000000000 : ℝ)^6265
        have hw : |(2388841793/5000000000 : ℝ)|=(2388841793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2634998563/10000000000 : ℝ)|^8313 ≤ (17038686988671/100000000000000 : ℝ)^6265
        have hw : |(-2634998563/10000000000 : ℝ)|=(2634998563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (84055523/200000000 : ℝ)*x 0 + (156105987/500000000 : ℝ)*x 1 + (2830559977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84055523/200000000 : ℝ)^8313 ≤ (15828580855673/50000000000000 : ℝ)^6265 := by
    have hnat : (84055523 : ℕ)^8313*50000000000000^6265 ≤ 15828580855673^6265*200000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84055523 200000000 15828580855673 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156105987/500000000 : ℝ)^8313 ≤ (21339656016087/100000000000000 : ℝ)^6265 := by
    have hnat : (156105987 : ℕ)^8313*100000000000000^6265 ≤ 21339656016087^6265*500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156105987 500000000 21339656016087 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830559977/5000000000 : ℝ)^8313 ≤ (23501591127313/50000000000000 : ℝ)^6265 := by
    have hnat : (2830559977 : ℕ)^8313*50000000000000^6265 ≤ 23501591127313^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830559977 5000000000 23501591127313 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84055523/200000000 : ℝ), (156105987/500000000 : ℝ), (2830559977/5000000000 : ℝ)] ![(15828580855673/50000000000000 : ℝ), (21339656016087/100000000000000 : ℝ), (23501591127313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84055523/200000000 : ℝ)|^8313 ≤ (15828580855673/50000000000000 : ℝ)^6265
        have hw : |(84055523/200000000 : ℝ)|=(84055523/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156105987/500000000 : ℝ)|^8313 ≤ (21339656016087/100000000000000 : ℝ)^6265
        have hw : |(156105987/500000000 : ℝ)|=(156105987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830559977/5000000000 : ℝ)|^8313 ≤ (23501591127313/50000000000000 : ℝ)^6265
        have hw : |(2830559977/5000000000 : ℝ)|=(2830559977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1904005151/10000000000 : ℝ)*x 0 + (4698008/9765625 : ℝ)*x 1 + (1506297589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904005151/10000000000 : ℝ)^8313 ≤ (442848211677/4000000000000 : ℝ)^6265 := by
    have hnat : (1904005151 : ℕ)^8313*4000000000000^6265 ≤ 442848211677^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904005151 10000000000 442848211677 4000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698008/9765625 : ℝ)^8313 ≤ (18936548300789/50000000000000 : ℝ)^6265 := by
    have hnat : (4698008 : ℕ)^8313*50000000000000^6265 ≤ 18936548300789^6265*9765625^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698008 9765625 18936548300789 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506297589/2500000000 : ℝ)^8313 ≤ (51055698084409/100000000000000 : ℝ)^6265 := by
    have hnat : (1506297589 : ℕ)^8313*100000000000000^6265 ≤ 51055698084409^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506297589 2500000000 51055698084409 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1904005151/10000000000 : ℝ), (4698008/9765625 : ℝ), (1506297589/2500000000 : ℝ)] ![(442848211677/4000000000000 : ℝ), (18936548300789/50000000000000 : ℝ), (51055698084409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1904005151/10000000000 : ℝ)|^8313 ≤ (442848211677/4000000000000 : ℝ)^6265
        have hw : |(-1904005151/10000000000 : ℝ)|=(1904005151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698008/9765625 : ℝ)|^8313 ≤ (18936548300789/50000000000000 : ℝ)^6265
        have hw : |(4698008/9765625 : ℝ)|=(4698008/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506297589/2500000000 : ℝ)|^8313 ≤ (51055698084409/100000000000000 : ℝ)^6265
        have hw : |(1506297589/2500000000 : ℝ)|=(1506297589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292465181/2500000000 : ℝ)*x 0 + (-1387492681/10000000000 : ℝ)*x 1 + (37657461/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292465181/2500000000 : ℝ)^8313 ≤ (20834658435349/50000000000000 : ℝ)^6265 := by
    have hnat : (1292465181 : ℕ)^8313*50000000000000^6265 ≤ 20834658435349^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292465181 2500000000 20834658435349 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387492681/10000000000 : ℝ)^8313 ≤ (7274946755091/100000000000000 : ℝ)^6265 := by
    have hnat : (1387492681 : ℕ)^8313*100000000000000^6265 ≤ 7274946755091^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387492681 10000000000 7274946755091 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37657461/62500000 : ℝ)^8313 ≤ (51055736358047/100000000000000 : ℝ)^6265 := by
    have hnat : (37657461 : ℕ)^8313*100000000000000^6265 ≤ 51055736358047^6265*62500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37657461 62500000 51055736358047 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292465181/2500000000 : ℝ), (-1387492681/10000000000 : ℝ), (37657461/62500000 : ℝ)] ![(20834658435349/50000000000000 : ℝ), (7274946755091/100000000000000 : ℝ), (51055736358047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292465181/2500000000 : ℝ)|^8313 ≤ (20834658435349/50000000000000 : ℝ)^6265
        have hw : |(1292465181/2500000000 : ℝ)|=(1292465181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387492681/10000000000 : ℝ)|^8313 ≤ (7274946755091/100000000000000 : ℝ)^6265
        have hw : |(-1387492681/10000000000 : ℝ)|=(1387492681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37657461/62500000 : ℝ)|^8313 ≤ (51055736358047/100000000000000 : ℝ)^6265
        have hw : |(37657461/62500000 : ℝ)|=(37657461/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169865039/10000000000 : ℝ)*x 0 + (376574421/625000000 : ℝ)*x 1 + (-693745467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169865039/10000000000 : ℝ)^8313 ≤ (20834681509467/50000000000000 : ℝ)^6265 := by
    have hnat : (5169865039 : ℕ)^8313*50000000000000^6265 ≤ 20834681509467^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169865039 10000000000 20834681509467 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376574421/625000000 : ℝ)^8313 ≤ (1595490698657/3125000000000 : ℝ)^6265 := by
    have hnat : (376574421 : ℕ)^8313*3125000000000^6265 ≤ 1595490698657^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376574421 625000000 1595490698657 3125000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693745467/5000000000 : ℝ)^8313 ≤ (1818733650207/25000000000000 : ℝ)^6265 := by
    have hnat : (693745467 : ℕ)^8313*25000000000000^6265 ≤ 1818733650207^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693745467 5000000000 1818733650207 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169865039/10000000000 : ℝ), (376574421/625000000 : ℝ), (-693745467/5000000000 : ℝ)] ![(20834681509467/50000000000000 : ℝ), (1595490698657/3125000000000 : ℝ), (1818733650207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169865039/10000000000 : ℝ)|^8313 ≤ (20834681509467/50000000000000 : ℝ)^6265
        have hw : |(5169865039/10000000000 : ℝ)|=(5169865039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376574421/625000000 : ℝ)|^8313 ≤ (1595490698657/3125000000000 : ℝ)^6265
        have hw : |(376574421/625000000 : ℝ)|=(376574421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-693745467/5000000000 : ℝ)|^8313 ≤ (1818733650207/25000000000000 : ℝ)^6265
        have hw : |(-693745467/5000000000 : ℝ)|=(693745467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s0_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (842619353/2000000000 : ℝ)*x 0 + (1398900657/2500000000 : ℝ)*x 1 + (3189938071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842619353/2000000000 : ℝ)^8313 ≤ (31760355173059/100000000000000 : ℝ)^6265 := by
    have hnat : (842619353 : ℕ)^8313*100000000000000^6265 ≤ 31760355173059^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842619353 2000000000 31760355173059 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398900657/2500000000 : ℝ)^8313 ≤ (46282749698317/100000000000000 : ℝ)^6265 := by
    have hnat : (1398900657 : ℕ)^8313*100000000000000^6265 ≤ 46282749698317^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398900657 2500000000 46282749698317 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189938071/10000000000 : ℝ)^8313 ≤ (5489223777999/25000000000000 : ℝ)^6265 := by
    have hnat : (3189938071 : ℕ)^8313*25000000000000^6265 ≤ 5489223777999^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189938071 10000000000 5489223777999 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842619353/2000000000 : ℝ), (1398900657/2500000000 : ℝ), (3189938071/10000000000 : ℝ)] ![(31760355173059/100000000000000 : ℝ), (46282749698317/100000000000000 : ℝ), (5489223777999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842619353/2000000000 : ℝ)|^8313 ≤ (31760355173059/100000000000000 : ℝ)^6265
        have hw : |(842619353/2000000000 : ℝ)|=(842619353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398900657/2500000000 : ℝ)|^8313 ≤ (46282749698317/100000000000000 : ℝ)^6265
        have hw : |(1398900657/2500000000 : ℝ)|=(1398900657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189938071/10000000000 : ℝ)|^8313 ≤ (5489223777999/25000000000000 : ℝ)^6265
        have hw : |(3189938071/10000000000 : ℝ)|=(3189938071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (279/1000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (1039/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1039 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1039*1^256 ≤ 0^256*1^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1039/256 : ℝ) ≤ (485236167136422007/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1039 ≤ (485236167136422007/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1039*20000000000000000000^256 ≤ 485236167136422007^256*5^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 485236167136422007 20000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (485236167136422007/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1039 := by
      have hnat : (1 : ℕ)^256*1^1039 ≤ 1^1039*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20485236167136422007/20000000000000000000 : ℝ) ≤ (402369599253117/400000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (20485236167136422007/20000000000000000000 : ℝ)^256 ≤ (402369599253117/400000000000000 : ℝ)^1039 := by
      have hnat : (20485236167136422007 : ℕ)^256*400000000000000^1039 ≤ 402369599253117^1039*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20485236167136422007 20000000000000000000 402369599253117 400000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402369599253117/400000000000000 : ℝ)) (X := (20485236167136422007/20000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10485236167136422007/10000000000000000000 : ℝ) ≤ (202369599253117/200000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (10485236167136422007/10000000000000000000 : ℝ)^256 ≤ (202369599253117/200000000000000 : ℝ)^1039 := by
      have hnat : (10485236167136422007 : ℕ)^256*200000000000000^1039 ≤ 202369599253117^1039*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10485236167136422007 10000000000000000000 202369599253117 200000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202369599253117/200000000000000 : ℝ)) (X := (10485236167136422007/10000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2369599253117/160000000000000 : ℝ)*(0 : ℝ))^(1039/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2369599253117/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(485236167136422007/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2369599253117/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (1 : ℝ)+(2369599253117/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(402369599253117/400000000000000 : ℝ) by norm_num, show 1+(485236167136422007/20000000000000000000 : ℝ)+(0 : ℝ)=(20485236167136422007/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(485236167136422007/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2369599253117/160000000000000 : ℝ)*(2/5 : ℝ))^(1039/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2369599253117/160000000000000 : ℝ)*(2/5 : ℝ)=(202369599253117/200000000000000 : ℝ) by norm_num, show 1+2*(485236167136422007/20000000000000000000 : ℝ)=(10485236167136422007/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2369599253117/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2369599253117/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2369599253117/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2369599253117/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2369599253117/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2369599253117/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1898793251/10000000000 : ℝ)*X 0 0+(6059428881/10000000000 : ℝ)*X 0 1+(1194420923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518032801/10000000000 : ℝ)*X 1 0+(-1317499291/5000000000 : ℝ)*X 1 1+(4777683727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518032951/10000000000 : ℝ)*X 2 0+(2388841793/5000000000 : ℝ)*X 2 1+(-2634998563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((84055523/200000000 : ℝ)*X 0 0+(156105987/500000000 : ℝ)*X 0 1+(2830559977/5000000000 : ℝ)*X 0 2+(84055523/200000000 : ℝ)*X 1 0+(156105987/500000000 : ℝ)*X 1 1+(2830559977/5000000000 : ℝ)*X 1 2+(84055523/200000000 : ℝ)*X 2 0+(156105987/500000000 : ℝ)*X 2 1+(2830559977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1904005151/10000000000 : ℝ)*X 0 0+(4698008/9765625 : ℝ)*X 0 1+(1506297589/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292465181/2500000000 : ℝ)*X 1 0+(-1387492681/10000000000 : ℝ)*X 1 1+(37657461/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169865039/10000000000 : ℝ)*X 2 0+(376574421/625000000 : ℝ)*X 2 1+(-693745467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842619353/2000000000 : ℝ)*X 0 0+(1398900657/2500000000 : ℝ)*X 0 1+(3189938071/10000000000 : ℝ)*X 0 2+(842619353/2000000000 : ℝ)*X 1 0+(1398900657/2500000000 : ℝ)*X 1 1+(3189938071/10000000000 : ℝ)*X 1 2+(842619353/2000000000 : ℝ)*X 2 0+(1398900657/2500000000 : ℝ)*X 2 1+(3189938071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15207974454924923183619/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6090459/25000000000000 : ℝ)*(base1) + (116184881/25000000000000 : ℝ)*(base19) + (28062123/6250000000000 : ℝ)*(base23) + (18476941/50000000000000 : ℝ)*(base24) + (55635009/50000000000000 : ℝ)*(upper3) + (587022973584469/100000000000000 : ℝ)*(major0) + (587022973584469/100000000000000 : ℝ)*(major1) + (587022973584469/100000000000000 : ℝ)*(major2) + (156037556487463/20000000000000 : ℝ)*(sp0) + (195047068869763/25000000000000 : ℝ)*(sp1) + (390094127135363/50000000000000 : ℝ)*(sp2) + (19692814261013/5000000000000 : ℝ)*(sp3) + (122767887/12500000000000 : ℝ)*(sp4) + (417000851/50000000000000 : ℝ)*(sp7) + (196928571791899/50000000000000 : ℝ)*(f.failure) + (48761796263661/6250000000000 : ℝ)*(f.sum) + (2396044712127/8000000000000000000000000000 : ℝ)*base66 + (3903436208127/16000000000000000000000000000 : ℝ)*base68 + (57704886431873/16000000000000000000000000000 : ℝ)*base69 + (71435331872127/16000000000000000000000000000 : ℝ)*base72 + (21595503103873/8000000000000000000000000000 : ℝ)*base73 + (34308515936127/16000000000000000000000000000 : ℝ)*base76 + (65328256256127/16000000000000000000000000000 : ℝ)*base78 + (33391028032127/16000000000000000000000000000 : ℝ)*base80 + (53869125887873/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6747057/5000000000000000000000 : ℝ)*base89 + (6747057/5000000000000000000000 : ℝ)*base91 + (6747057/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30635273661536800986687/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217891837/25000000000000 : ℝ)*(base19) + (419875147/20000000000000 : ℝ)*(base23) + (239846739/50000000000000 : ℝ)*(base39) + (17469429/6250000000000 : ℝ)*(upper3) + (37557181/12500000000000 : ℝ)*(upper5) + (154889387983619/25000000000000 : ℝ)*(major0) + (154889387983619/25000000000000 : ℝ)*(major1) + (309778536120499/50000000000000 : ℝ)*(major2) + (139163339/5000000000000 : ℝ)*(sp1) + (1945413837/50000000000000 : ℝ)*(sp2) + (411714239044033/50000000000000 : ℝ)*(sp4) + (823424823253939/100000000000000 : ℝ)*(sp5) + (164684593515627/20000000000000 : ℝ)*(sp6) + (25980368174591/6250000000000 : ℝ)*(sp7) + (25980368174591/6250000000000 : ℝ)*(f.failure) + (102928619722693/12500000000000 : ℝ)*(f.sum) + (1982039734229/8000000000000000000000000000 : ℝ)*base65 + (64617854974617/8000000000000000000000000000 : ℝ)*base68 + (4278788797577/4000000000000000000000000000 : ℝ)*base70 + (66721386302617/8000000000000000000000000000 : ℝ)*base72 + (8762232865771/8000000000000000000000000000 : ℝ)*base74 + (29406861613577/4000000000000000000000000000 : ℝ)*base76 + (7938081625577/4000000000000000000000000000 : ℝ)*base78 + (22308244077577/4000000000000000000000000000 : ℝ)*base80 + (1672425042423/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2266013/625000000000000000000 : ℝ)*base89 + (2266013/625000000000000000000 : ℝ)*base91 + (2266013/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (279/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s1_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105041673/10000000000 : ℝ)*x 0 + (2853717559/5000000000 : ℝ)*x 1 + (4997628131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105041673/10000000000 : ℝ)^8313 ≤ (1264846136587/10000000000000 : ℝ)^6265 := by
    have hnat : (2105041673 : ℕ)^8313*10000000000000^6265 ≤ 1264846136587^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105041673 10000000000 1264846136587 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2853717559/5000000000 : ℝ)^8313 ≤ (1900564617551/4000000000000 : ℝ)^6265 := by
    have hnat : (2853717559 : ℕ)^8313*4000000000000^6265 ≤ 1900564617551^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853717559 5000000000 1900564617551 4000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4997628131/10000000000 : ℝ)^8313 ≤ (39837423183921/100000000000000 : ℝ)^6265 := by
    have hnat : (4997628131 : ℕ)^8313*100000000000000^6265 ≤ 39837423183921^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997628131 10000000000 39837423183921 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105041673/10000000000 : ℝ), (2853717559/5000000000 : ℝ), (4997628131/10000000000 : ℝ)] ![(1264846136587/10000000000000 : ℝ), (1900564617551/4000000000000 : ℝ), (39837423183921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105041673/10000000000 : ℝ)|^8313 ≤ (1264846136587/10000000000000 : ℝ)^6265
        have hw : |(-2105041673/10000000000 : ℝ)|=(2105041673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2853717559/5000000000 : ℝ)|^8313 ≤ (1900564617551/4000000000000 : ℝ)^6265
        have hw : |(2853717559/5000000000 : ℝ)|=(2853717559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4997628131/10000000000 : ℝ)|^8313 ≤ (39837423183921/100000000000000 : ℝ)^6265
        have hw : |(4997628131/10000000000 : ℝ)|=(4997628131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420334741/10000000000 : ℝ)*x 0 + (-2488525339/10000000000 : ℝ)*x 1 + (62470349/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420334741/10000000000 : ℝ)^8313 ≤ (4436908294651/10000000000000 : ℝ)^6265 := by
    have hnat : (5420334741 : ℕ)^8313*10000000000000^6265 ≤ 4436908294651^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420334741 10000000000 4436908294651 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488525339/10000000000 : ℝ)^8313 ≤ (15793496079061/100000000000000 : ℝ)^6265 := by
    have hnat : (2488525339 : ℕ)^8313*100000000000000^6265 ≤ 15793496079061^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488525339 10000000000 15793496079061 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62470349/125000000 : ℝ)^8313 ≤ (19918710476083/50000000000000 : ℝ)^6265 := by
    have hnat : (62470349 : ℕ)^8313*50000000000000^6265 ≤ 19918710476083^6265*125000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62470349 125000000 19918710476083 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420334741/10000000000 : ℝ), (-2488525339/10000000000 : ℝ), (62470349/125000000 : ℝ)] ![(4436908294651/10000000000000 : ℝ), (15793496079061/100000000000000 : ℝ), (19918710476083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420334741/10000000000 : ℝ)|^8313 ≤ (4436908294651/10000000000000 : ℝ)^6265
        have hw : |(5420334741/10000000000 : ℝ)|=(5420334741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2488525339/10000000000 : ℝ)|^8313 ≤ (15793496079061/100000000000000 : ℝ)^6265
        have hw : |(-2488525339/10000000000 : ℝ)|=(2488525339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62470349/125000000 : ℝ)|^8313 ≤ (19918710476083/50000000000000 : ℝ)^6265
        have hw : |(62470349/125000000 : ℝ)|=(62470349/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355084061/2500000000 : ℝ)*x 0 + (2498813269/5000000000 : ℝ)*x 1 + (-2488525137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355084061/2500000000 : ℝ)^8313 ≤ (44369099271391/100000000000000 : ℝ)^6265 := by
    have hnat : (1355084061 : ℕ)^8313*100000000000000^6265 ≤ 44369099271391^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355084061 2500000000 44369099271391 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498813269/5000000000 : ℝ)^8313 ≤ (19918703167351/50000000000000 : ℝ)^6265 := by
    have hnat : (2498813269 : ℕ)^8313*50000000000000^6265 ≤ 19918703167351^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498813269 5000000000 19918703167351 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2488525137/10000000000 : ℝ)^8313 ≤ (7896747188991/50000000000000 : ℝ)^6265 := by
    have hnat : (2488525137 : ℕ)^8313*50000000000000^6265 ≤ 7896747188991^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488525137 10000000000 7896747188991 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355084061/2500000000 : ℝ), (2498813269/5000000000 : ℝ), (-2488525137/10000000000 : ℝ)] ![(44369099271391/100000000000000 : ℝ), (19918703167351/50000000000000 : ℝ), (7896747188991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355084061/2500000000 : ℝ)|^8313 ≤ (44369099271391/100000000000000 : ℝ)^6265
        have hw : |(1355084061/2500000000 : ℝ)|=(1355084061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498813269/5000000000 : ℝ)|^8313 ≤ (19918703167351/50000000000000 : ℝ)^6265
        have hw : |(2498813269/5000000000 : ℝ)|=(2498813269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2488525137/10000000000 : ℝ)|^8313 ≤ (7896747188991/50000000000000 : ℝ)^6265
        have hw : |(-2488525137/10000000000 : ℝ)|=(2488525137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134977953/312500000 : ℝ)*x 0 + (918220081/2500000000 : ℝ)*x 1 + (5078930133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134977953/312500000 : ℝ)^8313 ≤ (16413489750727/50000000000000 : ℝ)^6265 := by
    have hnat : (134977953 : ℕ)^8313*50000000000000^6265 ≤ 16413489750727^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134977953 312500000 16413489750727 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918220081/2500000000 : ℝ)^8313 ≤ (3309173098307/12500000000000 : ℝ)^6265 := by
    have hnat : (918220081 : ℕ)^8313*12500000000000^6265 ≤ 3309173098307^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918220081 2500000000 3309173098307 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078930133/10000000000 : ℝ)^8313 ≤ (40699635697923/100000000000000 : ℝ)^6265 := by
    have hnat : (5078930133 : ℕ)^8313*100000000000000^6265 ≤ 40699635697923^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078930133 10000000000 40699635697923 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134977953/312500000 : ℝ), (918220081/2500000000 : ℝ), (5078930133/10000000000 : ℝ)] ![(16413489750727/50000000000000 : ℝ), (3309173098307/12500000000000 : ℝ), (40699635697923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134977953/312500000 : ℝ)|^8313 ≤ (16413489750727/50000000000000 : ℝ)^6265
        have hw : |(134977953/312500000 : ℝ)|=(134977953/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(918220081/2500000000 : ℝ)|^8313 ≤ (3309173098307/12500000000000 : ℝ)^6265
        have hw : |(918220081/2500000000 : ℝ)|=(918220081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078930133/10000000000 : ℝ)|^8313 ≤ (40699635697923/100000000000000 : ℝ)^6265
        have hw : |(5078930133/10000000000 : ℝ)|=(5078930133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21058791/100000000 : ℝ)*x 0 + (1251850457/2500000000 : ℝ)*x 1 + (2848733177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21058791/100000000 : ℝ)^8313 ≤ (790946155097/6250000000000 : ℝ)^6265 := by
    have hnat : (21058791 : ℕ)^8313*6250000000000^6265 ≤ 790946155097^6265*100000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21058791 100000000 790946155097 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251850457/2500000000 : ℝ)^8313 ≤ (39940832964521/100000000000000 : ℝ)^6265 := by
    have hnat : (1251850457 : ℕ)^8313*100000000000000^6265 ≤ 39940832964521^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251850457 2500000000 39940832964521 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2848733177/5000000000 : ℝ)^8313 ≤ (47404028540523/100000000000000 : ℝ)^6265 := by
    have hnat : (2848733177 : ℕ)^8313*100000000000000^6265 ≤ 47404028540523^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848733177 5000000000 47404028540523 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21058791/100000000 : ℝ), (1251850457/2500000000 : ℝ), (2848733177/5000000000 : ℝ)] ![(790946155097/6250000000000 : ℝ), (39940832964521/100000000000000 : ℝ), (47404028540523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21058791/100000000 : ℝ)|^8313 ≤ (790946155097/6250000000000 : ℝ)^6265
        have hw : |(-21058791/100000000 : ℝ)|=(21058791/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251850457/2500000000 : ℝ)|^8313 ≤ (39940832964521/100000000000000 : ℝ)^6265
        have hw : |(1251850457/2500000000 : ℝ)|=(1251850457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2848733177/5000000000 : ℝ)|^8313 ≤ (47404028540523/100000000000000 : ℝ)^6265
        have hw : |(2848733177/5000000000 : ℝ)|=(2848733177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238554589/10000000000 : ℝ)*x 0 + (-1788686529/10000000000 : ℝ)*x 1 + (5697466131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238554589/10000000000 : ℝ)^8313 ≤ (1696223100049/4000000000000 : ℝ)^6265 := by
    have hnat : (5238554589 : ℕ)^8313*4000000000000^6265 ≤ 1696223100049^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238554589 10000000000 1696223100049 4000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788686529/10000000000 : ℝ)^8313 ≤ (5095198202629/50000000000000 : ℝ)^6265 := by
    have hnat : (1788686529 : ℕ)^8313*50000000000000^6265 ≤ 5095198202629^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788686529 10000000000 5095198202629 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5697466131/10000000000 : ℝ)^8313 ≤ (11851006519649/25000000000000 : ℝ)^6265 := by
    have hnat : (5697466131 : ℕ)^8313*25000000000000^6265 ≤ 11851006519649^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697466131 10000000000 11851006519649 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238554589/10000000000 : ℝ), (-1788686529/10000000000 : ℝ), (5697466131/10000000000 : ℝ)] ![(1696223100049/4000000000000 : ℝ), (5095198202629/50000000000000 : ℝ), (11851006519649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238554589/10000000000 : ℝ)|^8313 ≤ (1696223100049/4000000000000 : ℝ)^6265
        have hw : |(5238554589/10000000000 : ℝ)|=(5238554589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788686529/10000000000 : ℝ)|^8313 ≤ (5095198202629/50000000000000 : ℝ)^6265
        have hw : |(-1788686529/10000000000 : ℝ)|=(1788686529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5697466131/10000000000 : ℝ)|^8313 ≤ (11851006519649/25000000000000 : ℝ)^6265
        have hw : |(5697466131/10000000000 : ℝ)|=(5697466131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5115776/9765625 : ℝ)*x 0 + (2848733143/5000000000 : ℝ)*x 1 + (-1788686253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5115776/9765625 : ℝ)^8313 ≤ (42405577877163/100000000000000 : ℝ)^6265 := by
    have hnat : (5115776 : ℕ)^8313*100000000000000^6265 ≤ 42405577877163^6265*9765625^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115776 9765625 42405577877163 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848733143/5000000000 : ℝ)^8313 ≤ (47404027789801/100000000000000 : ℝ)^6265 := by
    have hnat : (2848733143 : ℕ)^8313*100000000000000^6265 ≤ 47404027789801^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848733143 5000000000 47404027789801 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788686253/10000000000 : ℝ)^8313 ≤ (5095197159417/50000000000000 : ℝ)^6265 := by
    have hnat : (1788686253 : ℕ)^8313*50000000000000^6265 ≤ 5095197159417^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788686253 10000000000 5095197159417 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5115776/9765625 : ℝ), (2848733143/5000000000 : ℝ), (-1788686253/10000000000 : ℝ)] ![(42405577877163/100000000000000 : ℝ), (47404027789801/100000000000000 : ℝ), (5095197159417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5115776/9765625 : ℝ)|^8313 ≤ (42405577877163/100000000000000 : ℝ)^6265
        have hw : |(5115776/9765625 : ℝ)|=(5115776/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848733143/5000000000 : ℝ)|^8313 ≤ (47404027789801/100000000000000 : ℝ)^6265
        have hw : |(2848733143/5000000000 : ℝ)|=(2848733143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1788686253/10000000000 : ℝ)|^8313 ≤ (5095197159417/50000000000000 : ℝ)^6265
        have hw : |(-1788686253/10000000000 : ℝ)|=(1788686253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s1_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864190229/2000000000 : ℝ)*x 0 + (1264892563/2500000000 : ℝ)*x 1 + (1846313209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864190229/2000000000 : ℝ)^8313 ≤ (4105460880321/12500000000000 : ℝ)^6265 := by
    have hnat : (864190229 : ℕ)^8313*12500000000000^6265 ≤ 4105460880321^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864190229 2000000000 4105460880321 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264892563/2500000000 : ℝ)^8313 ≤ (40493910837209/100000000000000 : ℝ)^6265 := by
    have hnat : (1264892563 : ℕ)^8313*100000000000000^6265 ≤ 40493910837209^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264892563 2500000000 40493910837209 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846313209/5000000000 : ℝ)^8313 ≤ (13331201052741/50000000000000 : ℝ)^6265 := by
    have hnat : (1846313209 : ℕ)^8313*50000000000000^6265 ≤ 13331201052741^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846313209 5000000000 13331201052741 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864190229/2000000000 : ℝ), (1264892563/2500000000 : ℝ), (1846313209/5000000000 : ℝ)] ![(4105460880321/12500000000000 : ℝ), (40493910837209/100000000000000 : ℝ), (13331201052741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864190229/2000000000 : ℝ)|^8313 ≤ (4105460880321/12500000000000 : ℝ)^6265
        have hw : |(864190229/2000000000 : ℝ)|=(864190229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1264892563/2500000000 : ℝ)|^8313 ≤ (40493910837209/100000000000000 : ℝ)^6265
        have hw : |(1264892563/2500000000 : ℝ)|=(1264892563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1846313209/5000000000 : ℝ)|^8313 ≤ (13331201052741/50000000000000 : ℝ)^6265
        have hw : |(1846313209/5000000000 : ℝ)|=(1846313209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (279/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (221/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10269/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (279/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (279/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (279/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (279/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (279/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (279/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (323/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (3888973009/50000000000000000000 : ℝ) := by
    have hpowers : (323/100000 : ℝ)^1039 ≤ (3888973009/50000000000000000000 : ℝ)^256 := by
      have hnat : (323 : ℕ)^1039*50000000000000000000^256 ≤ 3888973009^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        323 100000 3888973009 50000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (323/100000 : ℝ)) (X := (3888973009/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (279/1000 : ℝ) ^ (1039/256 : ℝ) ≤ (562254169071630437/100000000000000000000 : ℝ) := by
    have hpowers : (279/1000 : ℝ)^1039 ≤ (562254169071630437/100000000000000000000 : ℝ)^256 := by
      have hnat : (279 : ℕ)^1039*100000000000000000000^256 ≤ 562254169071630437^256*1000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 1000 562254169071630437 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/1000 : ℝ)) (X := (562254169071630437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000003888973009/25000000000000000000 : ℝ) ≤ (10000000000383283/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (25000000003888973009/25000000000000000000 : ℝ)^256 ≤ (10000000000383283/10000000000000000 : ℝ)^1039 := by
      have hnat : (25000000003888973009 : ℕ)^256*10000000000000000^1039 ≤ 10000000000383283^1039*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000003888973009 25000000000000000000 10000000000383283 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000383283/10000000000000000 : ℝ)) (X := (25000000003888973009/25000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20112450835369915291/20000000000000000000 : ℝ) ≤ (10013824169644201/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (20112450835369915291/20000000000000000000 : ℝ)^256 ≤ (10013824169644201/10000000000000000 : ℝ)^1039 := by
      have hnat : (20112450835369915291 : ℕ)^256*10000000000000000^1039 ≤ 10013824169644201^1039*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20112450835369915291 20000000000000000000 10013824169644201 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013824169644201/10000000000000000 : ℝ)) (X := (20112450835369915291/20000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50562254169071630437/50000000000000000000 : ℝ) ≤ (10027648338905119/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50562254169071630437/50000000000000000000 : ℝ)^256 ≤ (10027648338905119/10000000000000000 : ℝ)^1039 := by
      have hnat : (50562254169071630437 : ℕ)^256*10000000000000000^1039 ≤ 10027648338905119^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50562254169071630437 50000000000000000000 10027648338905119 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027648338905119/10000000000000000 : ℝ)) (X := (50562254169071630437/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3888973009/50000000000000000000 : ℝ) ≤ ((275761069597227242263/275770000000000000000 : ℝ)+2*(6912084630459/1378850000000000 : ℝ)*(323/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (275761069597227242263/275770000000000000000 : ℝ)+2*(6912084630459/1378850000000000 : ℝ)*(323/100000 : ℝ)=(10000000000383283/10000000000000000 : ℝ) by norm_num, show 1+2*(3888973009/50000000000000000000 : ℝ)=(25000000003888973009/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(562254169071630437/100000000000000000000 : ℝ)+(3888973009/50000000000000000000 : ℝ) ≤ ((275761069597227242263/275770000000000000000 : ℝ)+(6912084630459/1378850000000000 : ℝ)*((279/1000 : ℝ)+(323/100000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (275761069597227242263/275770000000000000000 : ℝ)+(6912084630459/1378850000000000 : ℝ)*((279/1000 : ℝ)+(323/100000 : ℝ))=(10013824169644201/10000000000000000 : ℝ) by norm_num, show 1+(562254169071630437/100000000000000000000 : ℝ)+(3888973009/50000000000000000000 : ℝ)=(20112450835369915291/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(562254169071630437/100000000000000000000 : ℝ) ≤ ((275761069597227242263/275770000000000000000 : ℝ)+2*(6912084630459/1378850000000000 : ℝ)*(279/1000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (275761069597227242263/275770000000000000000 : ℝ)+2*(6912084630459/1378850000000000 : ℝ)*(279/1000 : ℝ)=(10027648338905119/10000000000000000 : ℝ) by norm_num, show 1+2*(562254169071630437/100000000000000000000 : ℝ)=(50562254169071630437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275761069597227242263/275770000000000000000 : ℝ)*(X 1 0+X 2 0)+(6912084630459/1378850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (323/100000 : ℝ)) (hi := (279/1000 : ℝ)) (c := (275761069597227242263/275770000000000000000 : ℝ)) (alpha := (6912084630459/1378850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275761069597227242263/275770000000000000000 : ℝ)*(X 0 1+X 2 1)+(6912084630459/1378850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (323/100000 : ℝ)) (hi := (279/1000 : ℝ)) (c := (275761069597227242263/275770000000000000000 : ℝ)) (alpha := (6912084630459/1378850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275761069597227242263/275770000000000000000 : ℝ)*(X 0 2+X 1 2)+(6912084630459/1378850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (323/100000 : ℝ)) (hi := (279/1000 : ℝ)) (c := (275761069597227242263/275770000000000000000 : ℝ)) (alpha := (6912084630459/1378850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105041673/10000000000 : ℝ)*X 0 0+(2853717559/5000000000 : ℝ)*X 0 1+(4997628131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420334741/10000000000 : ℝ)*X 1 0+(-2488525339/10000000000 : ℝ)*X 1 1+(62470349/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355084061/2500000000 : ℝ)*X 2 0+(2498813269/5000000000 : ℝ)*X 2 1+(-2488525137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134977953/312500000 : ℝ)*X 0 0+(918220081/2500000000 : ℝ)*X 0 1+(5078930133/10000000000 : ℝ)*X 0 2+(134977953/312500000 : ℝ)*X 1 0+(918220081/2500000000 : ℝ)*X 1 1+(5078930133/10000000000 : ℝ)*X 1 2+(134977953/312500000 : ℝ)*X 2 0+(918220081/2500000000 : ℝ)*X 2 1+(5078930133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21058791/100000000 : ℝ)*X 0 0+(1251850457/2500000000 : ℝ)*X 0 1+(2848733177/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5238554589/10000000000 : ℝ)*X 1 0+(-1788686529/10000000000 : ℝ)*X 1 1+(5697466131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5115776/9765625 : ℝ)*X 2 0+(2848733143/5000000000 : ℝ)*X 2 1+(-1788686253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864190229/2000000000 : ℝ)*X 0 0+(1264892563/2500000000 : ℝ)*X 0 1+(1846313209/5000000000 : ℝ)*X 0 2+(864190229/2000000000 : ℝ)*X 1 0+(1264892563/2500000000 : ℝ)*X 1 1+(1846313209/5000000000 : ℝ)*X 1 2+(864190229/2000000000 : ℝ)*X 2 0+(1264892563/2500000000 : ℝ)*X 2 1+(1846313209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74744468753826973015671/8617812500000000000000000000 : ℝ) := by norm_num
    linear_combination (345839617/100000000000000 : ℝ)*(base1) + (799137743/50000000000000 : ℝ)*(base19) + (994466307/50000000000000 : ℝ)*(base23) + (1281361/2000000000000 : ℝ)*(upper3) + (239371331/100000000000000 : ℝ)*(upper5) + (1060031980864711/100000000000000 : ℝ)*(major0) + (1060031980864711/100000000000000 : ℝ)*(major1) + (1060031980864711/100000000000000 : ℝ)*(major2) + (176104829709911/12500000000000 : ℝ)*(sp0) + (176105538494759/12500000000000 : ℝ)*(sp1) + (88052744831309/6250000000000 : ℝ)*(sp2) + (71121503250319/10000000000000 : ℝ)*(sp3) + (7614393887/100000000000000 : ℝ)*(sp4) + (1194022309/50000000000000 : ℝ)*(sp7) + (28448710655497/4000000000000 : ℝ)*(f.failure) + (704422953116779/50000000000000 : ℝ)*(f.sum) + (94274658649797/34471250000000000000000000000 : ℝ)*base65 + (105260103288037719007/27577000000000000000000000000000000 : ℝ)*base68 + (37193796388545719007/27577000000000000000000000000000000 : ℝ)*base70 + (56544897339540280993/27577000000000000000000000000000000 : ℝ)*base71 + (94152958763591/68942500000000000000000000000 : ℝ)*base74 + (93357334479876280993/27577000000000000000000000000000000 : ℝ)*base75 + (80943958614227719007/27577000000000000000000000000000000 : ℝ)*base78 + (174961087817158280993/27577000000000000000000000000000000 : ℝ)*base79 + (19400108623893/8617812500000000000000000000 : ℝ)*base81 + (2352571/400000000000000000000 : ℝ)*base89 + (2352571/400000000000000000000 : ℝ)*base91 + (2352571/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260113918057101875543558247/34471250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801953/2000000000000 : ℝ)*(base1) + (838662029/50000000000000 : ℝ)*(base19) + (853035479/50000000000000 : ℝ)*(base23) + (33132637/20000000000000 : ℝ)*(upper3) + (169928419/100000000000000 : ℝ)*(upper5) + (2725873976423/250000000000 : ℝ)*(major0) + (2725873976423/250000000000 : ℝ)*(major1) + (2725873976423/250000000000 : ℝ)*(major2) + (1349919201/20000000000000 : ℝ)*(sp1) + (3649474997/50000000000000 : ℝ)*(sp2) + (362284989716143/25000000000000 : ℝ)*(sp4) + (724565720923429/50000000000000 : ℝ)*(sp5) + (144913086374597/10000000000000 : ℝ)*(sp6) + (365779485373211/50000000000000 : ℝ)*(sp7) + (91444882605509/12500000000000 : ℝ)*(f.failure) + (724569934383461/50000000000000 : ℝ)*(f.sum) + (1053091346489/2757700000000000000000000000 : ℝ)*base65 + (676313373569734751/68942500000000000000000000000000 : ℝ)*base68 + (41728905052395249/68942500000000000000000000000000 : ℝ)*base69 + (14404586760657251/68942500000000000000000000000000 : ℝ)*base72 + (127494281853439/27577000000000000000000000000 : ℝ)*base74 + (52786212754220249/68942500000000000000000000000000 : ℝ)*base75 + (186706148053589751/68942500000000000000000000000000 : ℝ)*base78 + (721503153755614751/68942500000000000000000000000000 : ℝ)*base80 + (5047122702613/3447125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1261713/1250000000000000000000 : ℝ)*base90 + (1261713/1250000000000000000000 : ℝ)*base92 + (1261713/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1120_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (279/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (221/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10269/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s2_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159468541/10000000000 : ℝ)*x 0 + (5515056301/10000000000 : ℝ)*x 1 + (5155420043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159468541/10000000000 : ℝ)^8313 ≤ (13084222035823/100000000000000 : ℝ)^6265 := by
    have hnat : (2159468541 : ℕ)^8313*100000000000000^6265 ≤ 13084222035823^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159468541 10000000000 13084222035823 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515056301/10000000000 : ℝ)^8313 ≤ (45400831284107/100000000000000 : ℝ)^6265 := by
    have hnat : (5515056301 : ℕ)^8313*100000000000000^6265 ≤ 45400831284107^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515056301 10000000000 45400831284107 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5155420043/10000000000 : ℝ)^8313 ≤ (20757473334741/50000000000000 : ℝ)^6265 := by
    have hnat : (5155420043 : ℕ)^8313*50000000000000^6265 ≤ 20757473334741^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155420043 10000000000 20757473334741 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159468541/10000000000 : ℝ), (5515056301/10000000000 : ℝ), (5155420043/10000000000 : ℝ)] ![(13084222035823/100000000000000 : ℝ), (45400831284107/100000000000000 : ℝ), (20757473334741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159468541/10000000000 : ℝ)|^8313 ≤ (13084222035823/100000000000000 : ℝ)^6265
        have hw : |(-2159468541/10000000000 : ℝ)|=(2159468541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515056301/10000000000 : ℝ)|^8313 ≤ (45400831284107/100000000000000 : ℝ)^6265
        have hw : |(5515056301/10000000000 : ℝ)|=(5515056301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5155420043/10000000000 : ℝ)|^8313 ≤ (20757473334741/50000000000000 : ℝ)^6265
        have hw : |(5155420043/10000000000 : ℝ)|=(5155420043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687408813/5000000000 : ℝ)*x 0 + (-586651691/2500000000 : ℝ)*x 1 + (2577710753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687408813/5000000000 : ℝ)^8313 ≤ (21937688618773/50000000000000 : ℝ)^6265 := by
    have hnat : (2687408813 : ℕ)^8313*50000000000000^6265 ≤ 21937688618773^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687408813 5000000000 21937688618773 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586651691/2500000000 : ℝ)^8313 ≤ (1826207554967/12500000000000 : ℝ)^6265 := by
    have hnat : (586651691 : ℕ)^8313*12500000000000^6265 ≤ 1826207554967^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586651691 2500000000 1826207554967 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2577710753/5000000000 : ℝ)^8313 ≤ (10378740575433/25000000000000 : ℝ)^6265 := by
    have hnat : (2577710753 : ℕ)^8313*25000000000000^6265 ≤ 10378740575433^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577710753 5000000000 10378740575433 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687408813/5000000000 : ℝ), (-586651691/2500000000 : ℝ), (2577710753/5000000000 : ℝ)] ![(21937688618773/50000000000000 : ℝ), (1826207554967/12500000000000 : ℝ), (10378740575433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687408813/5000000000 : ℝ)|^8313 ≤ (21937688618773/50000000000000 : ℝ)^6265
        have hw : |(2687408813/5000000000 : ℝ)|=(2687408813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-586651691/2500000000 : ℝ)|^8313 ≤ (1826207554967/12500000000000 : ℝ)^6265
        have hw : |(-586651691/2500000000 : ℝ)|=(586651691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2577710753/5000000000 : ℝ)|^8313 ≤ (10378740575433/25000000000000 : ℝ)^6265
        have hw : |(2577710753/5000000000 : ℝ)|=(2577710753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335926097/625000000 : ℝ)*x 0 + (5155421561/10000000000 : ℝ)*x 1 + (-2346606791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335926097/625000000 : ℝ)^8313 ≤ (8775075287201/20000000000000 : ℝ)^6265 := by
    have hnat : (335926097 : ℕ)^8313*20000000000000^6265 ≤ 8775075287201^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335926097 625000000 8775075287201 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155421561/10000000000 : ℝ)^8313 ≤ (4151496288941/10000000000000 : ℝ)^6265 := by
    have hnat : (5155421561 : ℕ)^8313*10000000000000^6265 ≤ 4151496288941^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155421561 10000000000 4151496288941 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2346606791/10000000000 : ℝ)^8313 ≤ (2921932132557/20000000000000 : ℝ)^6265 := by
    have hnat : (2346606791 : ℕ)^8313*20000000000000^6265 ≤ 2921932132557^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346606791 10000000000 2921932132557 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335926097/625000000 : ℝ), (5155421561/10000000000 : ℝ), (-2346606791/10000000000 : ℝ)] ![(8775075287201/20000000000000 : ℝ), (4151496288941/10000000000000 : ℝ), (2921932132557/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335926097/625000000 : ℝ)|^8313 ≤ (8775075287201/20000000000000 : ℝ)^6265
        have hw : |(335926097/625000000 : ℝ)|=(335926097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155421561/10000000000 : ℝ)|^8313 ≤ (4151496288941/10000000000000 : ℝ)^6265
        have hw : |(5155421561/10000000000 : ℝ)|=(5155421561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2346606791/10000000000 : ℝ)|^8313 ≤ (2921932132557/20000000000000 : ℝ)^6265
        have hw : |(-2346606791/10000000000 : ℝ)|=(2346606791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178287071/5000000000 : ℝ)*x 0 + (802975859/2000000000 : ℝ)*x 1 + (2363638327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178287071/5000000000 : ℝ)^8313 ≤ (2075215987743/6250000000000 : ℝ)^6265 := by
    have hnat : (2178287071 : ℕ)^8313*6250000000000^6265 ≤ 2075215987743^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178287071 5000000000 2075215987743 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802975859/2000000000 : ℝ)^8313 ≤ (14896520486967/50000000000000 : ℝ)^6265 := by
    have hnat : (802975859 : ℕ)^8313*50000000000000^6265 ≤ 14896520486967^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802975859 2000000000 14896520486967 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363638327/5000000000 : ℝ)^8313 ≤ (37003503203329/100000000000000 : ℝ)^6265 := by
    have hnat : (2363638327 : ℕ)^8313*100000000000000^6265 ≤ 37003503203329^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363638327 5000000000 37003503203329 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178287071/5000000000 : ℝ), (802975859/2000000000 : ℝ), (2363638327/5000000000 : ℝ)] ![(2075215987743/6250000000000 : ℝ), (14896520486967/50000000000000 : ℝ), (37003503203329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178287071/5000000000 : ℝ)|^8313 ≤ (2075215987743/6250000000000 : ℝ)^6265
        have hw : |(2178287071/5000000000 : ℝ)|=(2178287071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802975859/2000000000 : ℝ)|^8313 ≤ (14896520486967/50000000000000 : ℝ)^6265
        have hw : |(802975859/2000000000 : ℝ)|=(802975859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363638327/5000000000 : ℝ)|^8313 ≤ (37003503203329/100000000000000 : ℝ)^6265
        have hw : |(2363638327/5000000000 : ℝ)|=(2363638327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079788721/5000000000 : ℝ)*x 0 + (5157938731/10000000000 : ℝ)*x 1 + (344531999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079788721/5000000000 : ℝ)^8313 ≤ (13085097570147/100000000000000 : ℝ)^6265 := by
    have hnat : (1079788721 : ℕ)^8313*100000000000000^6265 ≤ 13085097570147^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079788721 5000000000 13085097570147 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157938731/10000000000 : ℝ)^8313 ≤ (20770930580561/50000000000000 : ℝ)^6265 := by
    have hnat : (5157938731 : ℕ)^8313*50000000000000^6265 ≤ 20770930580561^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157938731 10000000000 20770930580561 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344531999/625000000 : ℝ)^8313 ≤ (22686520626697/50000000000000 : ℝ)^6265 := by
    have hnat : (344531999 : ℕ)^8313*50000000000000^6265 ≤ 22686520626697^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344531999 625000000 22686520626697 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079788721/5000000000 : ℝ), (5157938731/10000000000 : ℝ), (344531999/625000000 : ℝ)] ![(13085097570147/100000000000000 : ℝ), (20770930580561/50000000000000 : ℝ), (22686520626697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079788721/5000000000 : ℝ)|^8313 ≤ (13085097570147/100000000000000 : ℝ)^6265
        have hw : |(-1079788721/5000000000 : ℝ)|=(1079788721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157938731/10000000000 : ℝ)|^8313 ≤ (20770930580561/50000000000000 : ℝ)^6265
        have hw : |(5157938731/10000000000 : ℝ)|=(5157938731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(344531999/625000000 : ℝ)|^8313 ≤ (22686520626697/50000000000000 : ℝ)^6265
        have hw : |(344531999/625000000 : ℝ)|=(344531999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132092581/250000000 : ℝ)*x 0 + (-1989514709/10000000000 : ℝ)*x 1 + (2756256243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132092581/250000000 : ℝ)^8313 ≤ (42891204882763/100000000000000 : ℝ)^6265 := by
    have hnat : (132092581 : ℕ)^8313*100000000000000^6265 ≤ 42891204882763^6265*250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132092581 250000000 42891204882763 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989514709/10000000000 : ℝ)^8313 ≤ (11735748371983/100000000000000 : ℝ)^6265 := by
    have hnat : (1989514709 : ℕ)^8313*100000000000000^6265 ≤ 11735748371983^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989514709 10000000000 11735748371983 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756256243/5000000000 : ℝ)^8313 ≤ (22686523368011/50000000000000 : ℝ)^6265 := by
    have hnat : (2756256243 : ℕ)^8313*50000000000000^6265 ≤ 22686523368011^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756256243 5000000000 22686523368011 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132092581/250000000 : ℝ), (-1989514709/10000000000 : ℝ), (2756256243/5000000000 : ℝ)] ![(42891204882763/100000000000000 : ℝ), (11735748371983/100000000000000 : ℝ), (22686523368011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132092581/250000000 : ℝ)|^8313 ≤ (42891204882763/100000000000000 : ℝ)^6265
        have hw : |(132092581/250000000 : ℝ)|=(132092581/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989514709/10000000000 : ℝ)|^8313 ≤ (11735748371983/100000000000000 : ℝ)^6265
        have hw : |(-1989514709/10000000000 : ℝ)|=(1989514709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756256243/5000000000 : ℝ)|^8313 ≤ (22686523368011/50000000000000 : ℝ)^6265
        have hw : |(2756256243/5000000000 : ℝ)|=(2756256243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165115691/312500000 : ℝ)*x 0 + (1378128099/2500000000 : ℝ)*x 1 + (-994758193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165115691/312500000 : ℝ)^8313 ≤ (21445596366391/50000000000000 : ℝ)^6265 := by
    have hnat : (165115691 : ℕ)^8313*50000000000000^6265 ≤ 21445596366391^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165115691 312500000 21445596366391 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378128099/2500000000 : ℝ)^8313 ≤ (1134326143827/2500000000000 : ℝ)^6265 := by
    have hnat : (1378128099 : ℕ)^8313*2500000000000^6265 ≤ 1134326143827^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378128099 2500000000 1134326143827 2500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994758193/5000000000 : ℝ)^8313 ≤ (2347152299603/20000000000000 : ℝ)^6265 := by
    have hnat : (994758193 : ℕ)^8313*20000000000000^6265 ≤ 2347152299603^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994758193 5000000000 2347152299603 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165115691/312500000 : ℝ), (1378128099/2500000000 : ℝ), (-994758193/5000000000 : ℝ)] ![(21445596366391/50000000000000 : ℝ), (1134326143827/2500000000000 : ℝ), (2347152299603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165115691/312500000 : ℝ)|^8313 ≤ (21445596366391/50000000000000 : ℝ)^6265
        have hw : |(165115691/312500000 : ℝ)|=(165115691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378128099/2500000000 : ℝ)|^8313 ≤ (1134326143827/2500000000000 : ℝ)^6265
        have hw : |(1378128099/2500000000 : ℝ)|=(1378128099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-994758193/5000000000 : ℝ)|^8313 ≤ (2347152299603/20000000000000 : ℝ)^6265
        have hw : |(-994758193/5000000000 : ℝ)|=(994758193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s2_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356789543/10000000000 : ℝ)*x 0 + (4722288479/10000000000 : ℝ)*x 1 + (1004979471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356789543/10000000000 : ℝ)^8313 ≤ (16602817073051/50000000000000 : ℝ)^6265 := by
    have hnat : (4356789543 : ℕ)^8313*50000000000000^6265 ≤ 16602817073051^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356789543 10000000000 16602817073051 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4722288479/10000000000 : ℝ)^8313 ≤ (36951702544579/100000000000000 : ℝ)^6265 := by
    have hnat : (4722288479 : ℕ)^8313*100000000000000^6265 ≤ 36951702544579^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722288479 10000000000 36951702544579 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004979471/2500000000 : ℝ)^8313 ≤ (14921331644967/50000000000000 : ℝ)^6265 := by
    have hnat : (1004979471 : ℕ)^8313*50000000000000^6265 ≤ 14921331644967^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004979471 2500000000 14921331644967 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356789543/10000000000 : ℝ), (4722288479/10000000000 : ℝ), (1004979471/2500000000 : ℝ)] ![(16602817073051/50000000000000 : ℝ), (36951702544579/100000000000000 : ℝ), (14921331644967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356789543/10000000000 : ℝ)|^8313 ≤ (16602817073051/50000000000000 : ℝ)^6265
        have hw : |(4356789543/10000000000 : ℝ)|=(4356789543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4722288479/10000000000 : ℝ)|^8313 ≤ (36951702544579/100000000000000 : ℝ)^6265
        have hw : |(4722288479/10000000000 : ℝ)|=(4722288479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004979471/2500000000 : ℝ)|^8313 ≤ (14921331644967/50000000000000 : ℝ)^6265
        have hw : |(1004979471/2500000000 : ℝ)|=(1004979471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (8969/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16569/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10269/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (221/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10269/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (221/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10269/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (221/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10269/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (221/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10269/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (221/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10269/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (221/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (221/4000 : ℝ) ^ (1039/256 : ℝ) ≤ (786389419432433/100000000000000000000 : ℝ) := by
    have hpowers : (221/4000 : ℝ)^1039 ≤ (786389419432433/100000000000000000000 : ℝ)^256 := by
      have hnat : (221 : ℕ)^1039*100000000000000000000^256 ≤ 786389419432433^256*4000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        221 4000 786389419432433 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (221/4000 : ℝ)) (X := (786389419432433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (10269/50000 : ℝ) ^ (1039/256 : ℝ) ≤ (40540846335227689/25000000000000000000 : ℝ) := by
    have hpowers : (10269/50000 : ℝ)^1039 ≤ (40540846335227689/25000000000000000000 : ℝ)^256 := by
      have hnat : (10269 : ℕ)^1039*25000000000000000000^256 ≤ 40540846335227689^256*50000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10269 50000 40540846335227689 25000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10269/50000 : ℝ)) (X := (40540846335227689/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000786389419432433/50000000000000000000 : ℝ) ≤ (312501210987117/312500000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50000786389419432433/50000000000000000000 : ℝ)^256 ≤ (312501210987117/312500000000000 : ℝ)^1039 := by
      have hnat : (50000786389419432433 : ℕ)^256*312500000000000^1039 ≤ 312501210987117^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000786389419432433 50000000000000000000 312501210987117 312500000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501210987117/312500000000000 : ℝ)) (X := (50000786389419432433/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100162949774760343189/100000000000000000000 : ℝ) ≤ (1000401246905827/1000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (100162949774760343189/100000000000000000000 : ℝ)^256 ≤ (1000401246905827/1000000000000000 : ℝ)^1039 := by
      have hnat : (100162949774760343189 : ℕ)^256*1000000000000000^1039 ≤ 1000401246905827^1039*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100162949774760343189 100000000000000000000 1000401246905827 1000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000401246905827/1000000000000000 : ℝ)) (X := (100162949774760343189/100000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12540540846335227689/12500000000000000000 : ℝ) ≤ (2501996546632199/2500000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (12540540846335227689/12500000000000000000 : ℝ)^256 ≤ (2501996546632199/2500000000000000 : ℝ)^1039 := by
      have hnat : (12540540846335227689 : ℕ)^256*2500000000000000^1039 ≤ 2501996546632199^1039*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12540540846335227689 12500000000000000000 2501996546632199 2500000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501996546632199/2500000000000000 : ℝ)) (X := (12540540846335227689/12500000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(786389419432433/100000000000000000000 : ℝ) ≤ ((37521668049884372093/37532500000000000000 : ℝ)+2*(1986858735263/750650000000000 : ℝ)*(221/4000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (37521668049884372093/37532500000000000000 : ℝ)+2*(1986858735263/750650000000000 : ℝ)*(221/4000 : ℝ)=(312501210987117/312500000000000 : ℝ) by norm_num, show 1+2*(786389419432433/100000000000000000000 : ℝ)=(50000786389419432433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40540846335227689/25000000000000000000 : ℝ)+(786389419432433/100000000000000000000 : ℝ) ≤ ((37521668049884372093/37532500000000000000 : ℝ)+(1986858735263/750650000000000 : ℝ)*((10269/50000 : ℝ)+(221/4000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (37521668049884372093/37532500000000000000 : ℝ)+(1986858735263/750650000000000 : ℝ)*((10269/50000 : ℝ)+(221/4000 : ℝ))=(1000401246905827/1000000000000000 : ℝ) by norm_num, show 1+(40540846335227689/25000000000000000000 : ℝ)+(786389419432433/100000000000000000000 : ℝ)=(100162949774760343189/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40540846335227689/25000000000000000000 : ℝ) ≤ ((37521668049884372093/37532500000000000000 : ℝ)+2*(1986858735263/750650000000000 : ℝ)*(10269/50000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (37521668049884372093/37532500000000000000 : ℝ)+2*(1986858735263/750650000000000 : ℝ)*(10269/50000 : ℝ)=(2501996546632199/2500000000000000 : ℝ) by norm_num, show 1+2*(40540846335227689/25000000000000000000 : ℝ)=(12540540846335227689/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37521668049884372093/37532500000000000000 : ℝ)*(X 1 0+X 2 0)+(1986858735263/750650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (221/4000 : ℝ)) (hi := (10269/50000 : ℝ)) (c := (37521668049884372093/37532500000000000000 : ℝ)) (alpha := (1986858735263/750650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37521668049884372093/37532500000000000000 : ℝ)*(X 0 1+X 2 1)+(1986858735263/750650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (221/4000 : ℝ)) (hi := (10269/50000 : ℝ)) (c := (37521668049884372093/37532500000000000000 : ℝ)) (alpha := (1986858735263/750650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37521668049884372093/37532500000000000000 : ℝ)*(X 0 2+X 1 2)+(1986858735263/750650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (221/4000 : ℝ)) (hi := (10269/50000 : ℝ)) (c := (37521668049884372093/37532500000000000000 : ℝ)) (alpha := (1986858735263/750650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2159468541/10000000000 : ℝ)*X 0 0+(5515056301/10000000000 : ℝ)*X 0 1+(5155420043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687408813/5000000000 : ℝ)*X 1 0+(-586651691/2500000000 : ℝ)*X 1 1+(2577710753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335926097/625000000 : ℝ)*X 2 0+(5155421561/10000000000 : ℝ)*X 2 1+(-2346606791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178287071/5000000000 : ℝ)*X 0 0+(802975859/2000000000 : ℝ)*X 0 1+(2363638327/5000000000 : ℝ)*X 0 2+(2178287071/5000000000 : ℝ)*X 1 0+(802975859/2000000000 : ℝ)*X 1 1+(2363638327/5000000000 : ℝ)*X 1 2+(2178287071/5000000000 : ℝ)*X 2 0+(802975859/2000000000 : ℝ)*X 2 1+(2363638327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079788721/5000000000 : ℝ)*X 0 0+(5157938731/10000000000 : ℝ)*X 0 1+(344531999/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132092581/250000000 : ℝ)*X 1 0+(-1989514709/10000000000 : ℝ)*X 1 1+(2756256243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165115691/312500000 : ℝ)*X 2 0+(1378128099/2500000000 : ℝ)*X 2 1+(-994758193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356789543/10000000000 : ℝ)*X 0 0+(4722288479/10000000000 : ℝ)*X 0 1+(1004979471/2500000000 : ℝ)*X 0 2+(4356789543/10000000000 : ℝ)*X 1 0+(4722288479/10000000000 : ℝ)*X 1 1+(1004979471/2500000000 : ℝ)*X 1 2+(4356789543/10000000000 : ℝ)*X 2 0+(4722288479/10000000000 : ℝ)*X 2 1+(1004979471/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3761629840279200907026507597/375325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245299553/20000000000000 : ℝ)*(base19) + (469746243/50000000000000 : ℝ)*(base23) + (6809239/2500000000000 : ℝ)*(upper3) + (66841723/50000000000000 : ℝ)*(upper4) + (11396933/20000000000000 : ℝ)*(upper5) + (418435660083519/20000000000000 : ℝ)*(major0) + (418435660083519/20000000000000 : ℝ)*(major1) + (418435660083519/20000000000000 : ℝ)*(major2) + (21723515100287/781250000000 : ℝ)*(sp0) + (2780629110695521/100000000000000 : ℝ)*(sp1) + (1737893373563/62500000000 : ℝ)*(sp2) + (14037174120793/1000000000000 : ℝ)*(sp3) + (20404356549/100000000000000 : ℝ)*(sp4) + (1703497007/20000000000000 : ℝ)*(sp7) + (280745185912867/20000000000000 : ℝ)*(f.failure) + (1390315168596643/50000000000000 : ℝ)*(f.sum) + (48144217181029/15013000000000000000000000000 : ℝ)*base66 + (5042739094999685267/750650000000000000000000000000000 : ℝ)*base67 + (2093410560625085267/750650000000000000000000000000000 : ℝ)*base69 + (919174960739535267/750650000000000000000000000000000 : ℝ)*base71 + (3502182669879/15013000000000000000000000000 : ℝ)*base74 + (3002604024479785267/750650000000000000000000000000000 : ℝ)*base75 + (3250402267744435267/750650000000000000000000000000000 : ℝ)*base77 + (1105372706885435267/750650000000000000000000000000000 : ℝ)*base79 + (26815250689213/7506500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (8878519/2000000000000000000000 : ℝ)*base90 + (8878519/2000000000000000000000 : ℝ)*base92 + (8878519/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76482363746777619982731/15013000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853233091/100000000000000 : ℝ)*(base19) + (17495541/4000000000000 : ℝ)*(base23) + (54410103/25000000000000 : ℝ)*(upper2) + (949419/5000000000000 : ℝ)*(upper3) + (1382087/800000000000 : ℝ)*(upper5) + (424403535988497/20000000000000 : ℝ)*(major0) + (424403535988497/20000000000000 : ℝ)*(major1) + (424403535988497/20000000000000 : ℝ)*(major2) + (14155423443/100000000000000 : ℝ)*(sp1) + (1069463327/100000000000000 : ℝ)*(sp2) + (1410144414883029/50000000000000 : ℝ)*(sp4) + (112810952844381/4000000000000 : ℝ)*(sp5) + (1410143661457103/50000000000000 : ℝ)*(sp6) + (1423746360305271/100000000000000 : ℝ)*(sp7) + (1423746360305271/100000000000000 : ℝ)*(f.failure) + (1410144414883029/50000000000000 : ℝ)*(f.sum) + (2696285056701/15013000000000000000000000000 : ℝ)*base65 + (2821820633233185779/750650000000000000000000000000000 : ℝ)*base68 + (1100520463737964221/750650000000000000000000000000000 : ℝ)*base69 + (2944839605354785779/750650000000000000000000000000000 : ℝ)*base72 + (20152602427647/7506500000000000000000000000 : ℝ)*base74 + (7061563644165435779/750650000000000000000000000000000 : ℝ)*base76 + (921344742827514221/750650000000000000000000000000000 : ℝ)*base77 + (1752116043910564221/750650000000000000000000000000000 : ℝ)*base79 + (53244817740339/15013000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12786747/10000000000000000000000 : ℝ)*base90 + (12786747/10000000000000000000000 : ℝ)*base92 + (12786747/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1120_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1120_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1120_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1120_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1120_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
