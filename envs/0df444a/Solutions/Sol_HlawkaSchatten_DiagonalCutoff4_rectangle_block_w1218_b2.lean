-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:47.034855+00:00
-- url     : https://prove2.me/submissions/3f12162e-f66a-47d4-86ca-ba3f880697fc

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
theorem support_rectangle_w1218_s6_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131043579/10000000000 : ℝ)*x 0 + (539186569/1000000000 : ℝ)*x 1 + (658334503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131043579/10000000000 : ℝ)^8411 ≤ (6478322355857/50000000000000 : ℝ)^6363 := by
    have hnat : (2131043579 : ℕ)^8411*50000000000000^6363 ≤ 6478322355857^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131043579 10000000000 6478322355857 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539186569/1000000000 : ℝ)^8411 ≤ (5524670878969/12500000000000 : ℝ)^6363 := by
    have hnat : (539186569 : ℕ)^8411*12500000000000^6363 ≤ 5524670878969^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539186569 1000000000 5524670878969 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658334503/1250000000 : ℝ)^8411 ≤ (21422994118497/50000000000000 : ℝ)^6363 := by
    have hnat : (658334503 : ℕ)^8411*50000000000000^6363 ≤ 21422994118497^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658334503 1250000000 21422994118497 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131043579/10000000000 : ℝ), (539186569/1000000000 : ℝ), (658334503/1250000000 : ℝ)] ![(6478322355857/50000000000000 : ℝ), (5524670878969/12500000000000 : ℝ), (21422994118497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131043579/10000000000 : ℝ)|^8411 ≤ (6478322355857/50000000000000 : ℝ)^6363
        have hw : |(-2131043579/10000000000 : ℝ)|=(2131043579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539186569/1000000000 : ℝ)|^8411 ≤ (5524670878969/12500000000000 : ℝ)^6363
        have hw : |(539186569/1000000000 : ℝ)|=(539186569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658334503/1250000000 : ℝ)|^8411 ≤ (21422994118497/50000000000000 : ℝ)^6363
        have hw : |(658334503/1250000000 : ℝ)|=(658334503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534448743/1000000000 : ℝ)*x 0 + (-43890537/200000000 : ℝ)*x 1 + (1316668947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534448743/1000000000 : ℝ)^8411 ≤ (5460591784129/12500000000000 : ℝ)^6363 := by
    have hnat : (534448743 : ℕ)^8411*12500000000000^6363 ≤ 5460591784129^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534448743 1000000000 5460591784129 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43890537/200000000 : ℝ)^8411 ≤ (6734640006299/50000000000000 : ℝ)^6363 := by
    have hnat : (43890537 : ℕ)^8411*50000000000000^6363 ≤ 6734640006299^6363*200000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43890537 200000000 6734640006299 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316668947/2500000000 : ℝ)^8411 ≤ (5355748212389/12500000000000 : ℝ)^6363 := by
    have hnat : (1316668947 : ℕ)^8411*12500000000000^6363 ≤ 5355748212389^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316668947 2500000000 5355748212389 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534448743/1000000000 : ℝ), (-43890537/200000000 : ℝ), (1316668947/2500000000 : ℝ)] ![(5460591784129/12500000000000 : ℝ), (6734640006299/50000000000000 : ℝ), (5355748212389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534448743/1000000000 : ℝ)|^8411 ≤ (5460591784129/12500000000000 : ℝ)^6363
        have hw : |(534448743/1000000000 : ℝ)|=(534448743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43890537/200000000 : ℝ)|^8411 ≤ (6734640006299/50000000000000 : ℝ)^6363
        have hw : |(-43890537/200000000 : ℝ)|=(43890537/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316668947/2500000000 : ℝ)|^8411 ≤ (5355748212389/12500000000000 : ℝ)^6363
        have hw : |(1316668947/2500000000 : ℝ)|=(1316668947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344487331/10000000000 : ℝ)*x 0 + (1316668969/2500000000 : ℝ)*x 1 + (-1097263433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344487331/10000000000 : ℝ)^8411 ≤ (349477865627/800000000000 : ℝ)^6363 := by
    have hnat : (5344487331 : ℕ)^8411*800000000000^6363 ≤ 349477865627^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344487331 10000000000 349477865627 800000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316668969/2500000000 : ℝ)^8411 ≤ (42845986645441/100000000000000 : ℝ)^6363 := by
    have hnat : (1316668969 : ℕ)^8411*100000000000000^6363 ≤ 42845986645441^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316668969 2500000000 42845986645441 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097263433/5000000000 : ℝ)^8411 ≤ (13469280142409/100000000000000 : ℝ)^6363 := by
    have hnat : (1097263433 : ℕ)^8411*100000000000000^6363 ≤ 13469280142409^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097263433 5000000000 13469280142409 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344487331/10000000000 : ℝ), (1316668969/2500000000 : ℝ), (-1097263433/5000000000 : ℝ)] ![(349477865627/800000000000 : ℝ), (42845986645441/100000000000000 : ℝ), (13469280142409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344487331/10000000000 : ℝ)|^8411 ≤ (349477865627/800000000000 : ℝ)^6363
        have hw : |(5344487331/10000000000 : ℝ)|=(5344487331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316668969/2500000000 : ℝ)|^8411 ≤ (42845986645441/100000000000000 : ℝ)^6363
        have hw : |(1316668969/2500000000 : ℝ)|=(1316668969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097263433/5000000000 : ℝ)|^8411 ≤ (13469280142409/100000000000000 : ℝ)^6363
        have hw : |(-1097263433/5000000000 : ℝ)|=(1097263433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354064107/10000000000 : ℝ)*x 0 + (845893553/2000000000 : ℝ)*x 1 + (448224787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354064107/10000000000 : ℝ)^8411 ≤ (3331725647389/10000000000000 : ℝ)^6363 := by
    have hnat : (4354064107 : ℕ)^8411*10000000000000^6363 ≤ 3331725647389^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354064107 10000000000 3331725647389 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845893553/2000000000 : ℝ)^8411 ≤ (32062823022403/100000000000000 : ℝ)^6363 := by
    have hnat : (845893553 : ℕ)^8411*100000000000000^6363 ≤ 32062823022403^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845893553 2000000000 32062823022403 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448224787/1000000000 : ℝ)^8411 ≤ (34619920487103/100000000000000 : ℝ)^6363 := by
    have hnat : (448224787 : ℕ)^8411*100000000000000^6363 ≤ 34619920487103^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448224787 1000000000 34619920487103 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354064107/10000000000 : ℝ), (845893553/2000000000 : ℝ), (448224787/1000000000 : ℝ)] ![(3331725647389/10000000000000 : ℝ), (32062823022403/100000000000000 : ℝ), (34619920487103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354064107/10000000000 : ℝ)|^8411 ≤ (3331725647389/10000000000000 : ℝ)^6363
        have hw : |(4354064107/10000000000 : ℝ)|=(4354064107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845893553/2000000000 : ℝ)|^8411 ≤ (32062823022403/100000000000000 : ℝ)^6363
        have hw : |(845893553/2000000000 : ℝ)|=(845893553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448224787/1000000000 : ℝ)|^8411 ≤ (34619920487103/100000000000000 : ℝ)^6363
        have hw : |(448224787/1000000000 : ℝ)|=(448224787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131048441/10000000000 : ℝ)*x 0 + (42135939/80000000 : ℝ)*x 1 + (539154811/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131048441/10000000000 : ℝ)^8411 ≤ (12956683786899/100000000000000 : ℝ)^6363 := by
    have hnat : (2131048441 : ℕ)^8411*100000000000000^6363 ≤ 12956683786899^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131048441 10000000000 12956683786899 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42135939/80000000 : ℝ)^8411 ≤ (42849390224229/100000000000000 : ℝ)^6363 := by
    have hnat : (42135939 : ℕ)^8411*100000000000000^6363 ≤ 42849390224229^6363*80000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42135939 80000000 42849390224229 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539154811/1000000000 : ℝ)^8411 ≤ (22096962986571/50000000000000 : ℝ)^6363 := by
    have hnat : (539154811 : ℕ)^8411*50000000000000^6363 ≤ 22096962986571^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539154811 1000000000 22096962986571 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131048441/10000000000 : ℝ), (42135939/80000000 : ℝ), (539154811/1000000000 : ℝ)] ![(12956683786899/100000000000000 : ℝ), (42849390224229/100000000000000 : ℝ), (22096962986571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131048441/10000000000 : ℝ)|^8411 ≤ (12956683786899/100000000000000 : ℝ)^6363
        have hw : |(-2131048441/10000000000 : ℝ)|=(2131048441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42135939/80000000 : ℝ)|^8411 ≤ (42849390224229/100000000000000 : ℝ)^6363
        have hw : |(42135939/80000000 : ℝ)|=(42135939/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539154811/1000000000 : ℝ)|^8411 ≤ (22096962986571/50000000000000 : ℝ)^6363
        have hw : |(539154811/1000000000 : ℝ)|=(539154811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106251939/200000000 : ℝ)*x 0 + (-2069654599/10000000000 : ℝ)*x 1 + (5391548099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106251939/200000000 : ℝ)^8411 ≤ (43340501195403/100000000000000 : ℝ)^6363 := by
    have hnat : (106251939 : ℕ)^8411*100000000000000^6363 ≤ 43340501195403^6363*200000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106251939 200000000 43340501195403 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069654599/10000000000 : ℝ)^8411 ≤ (6232786466651/50000000000000 : ℝ)^6363 := by
    have hnat : (2069654599 : ℕ)^8411*50000000000000^6363 ≤ 6232786466651^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069654599 10000000000 6232786466651 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391548099/10000000000 : ℝ)^8411 ≤ (8838785170791/20000000000000 : ℝ)^6363 := by
    have hnat : (5391548099 : ℕ)^8411*20000000000000^6363 ≤ 8838785170791^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391548099 10000000000 8838785170791 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106251939/200000000 : ℝ), (-2069654599/10000000000 : ℝ), (5391548099/10000000000 : ℝ)] ![(43340501195403/100000000000000 : ℝ), (6232786466651/50000000000000 : ℝ), (8838785170791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106251939/200000000 : ℝ)|^8411 ≤ (43340501195403/100000000000000 : ℝ)^6363
        have hw : |(106251939/200000000 : ℝ)|=(106251939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069654599/10000000000 : ℝ)|^8411 ≤ (6232786466651/50000000000000 : ℝ)^6363
        have hw : |(-2069654599/10000000000 : ℝ)|=(2069654599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391548099/10000000000 : ℝ)|^8411 ≤ (8838785170791/20000000000000 : ℝ)^6363
        have hw : |(5391548099/10000000000 : ℝ)|=(5391548099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656298473/5000000000 : ℝ)*x 0 + (673943513/1250000000 : ℝ)*x 1 + (-2069654599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656298473/5000000000 : ℝ)^8411 ≤ (43340501152267/100000000000000 : ℝ)^6363 := by
    have hnat : (2656298473 : ℕ)^8411*100000000000000^6363 ≤ 43340501152267^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656298473 5000000000 43340501152267 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673943513/1250000000 : ℝ)^8411 ≤ (44193925908131/100000000000000 : ℝ)^6363 := by
    have hnat : (673943513 : ℕ)^8411*100000000000000^6363 ≤ 44193925908131^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673943513 1250000000 44193925908131 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069654599/10000000000 : ℝ)^8411 ≤ (6232786466651/50000000000000 : ℝ)^6363 := by
    have hnat : (2069654599 : ℕ)^8411*50000000000000^6363 ≤ 6232786466651^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069654599 10000000000 6232786466651 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656298473/5000000000 : ℝ), (673943513/1250000000 : ℝ), (-2069654599/10000000000 : ℝ)] ![(43340501152267/100000000000000 : ℝ), (44193925908131/100000000000000 : ℝ), (6232786466651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656298473/5000000000 : ℝ)|^8411 ≤ (43340501152267/100000000000000 : ℝ)^6363
        have hw : |(2656298473/5000000000 : ℝ)|=(2656298473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673943513/1250000000 : ℝ)|^8411 ≤ (44193925908131/100000000000000 : ℝ)^6363
        have hw : |(673943513/1250000000 : ℝ)|=(673943513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069654599/10000000000 : ℝ)|^8411 ≤ (6232786466651/50000000000000 : ℝ)^6363
        have hw : |(-2069654599/10000000000 : ℝ)|=(2069654599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s6_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272129619/625000000 : ℝ)*x 0 + (4481608733/10000000000 : ℝ)*x 1 + (1057527259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272129619/625000000 : ℝ)^8411 ≤ (6663471113853/20000000000000 : ℝ)^6363 := by
    have hnat : (272129619 : ℕ)^8411*20000000000000^6363 ≤ 6663471113853^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272129619 625000000 6663471113853 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481608733/10000000000 : ℝ)^8411 ≤ (8653348798967/25000000000000 : ℝ)^6363 := by
    have hnat : (4481608733 : ℕ)^8411*25000000000000^6363 ≤ 8653348798967^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481608733 10000000000 8653348798967 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057527259/2500000000 : ℝ)^8411 ≤ (32069249218071/100000000000000 : ℝ)^6363 := by
    have hnat : (1057527259 : ℕ)^8411*100000000000000^6363 ≤ 32069249218071^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057527259 2500000000 32069249218071 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272129619/625000000 : ℝ), (4481608733/10000000000 : ℝ), (1057527259/2500000000 : ℝ)] ![(6663471113853/20000000000000 : ℝ), (8653348798967/25000000000000 : ℝ), (32069249218071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272129619/625000000 : ℝ)|^8411 ≤ (6663471113853/20000000000000 : ℝ)^6363
        have hw : |(272129619/625000000 : ℝ)|=(272129619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481608733/10000000000 : ℝ)|^8411 ≤ (8653348798967/25000000000000 : ℝ)^6363
        have hw : |(4481608733/10000000000 : ℝ)|=(4481608733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057527259/2500000000 : ℝ)|^8411 ≤ (32069249218071/100000000000000 : ℝ)^6363
        have hw : |(1057527259/2500000000 : ℝ)|=(1057527259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2289/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5711/50000 : ℝ) ^ (4205/1024 : ℝ) ≤ (13510446207449929/100000000000000000000 : ℝ) := by
    have hpowers : (5711/50000 : ℝ)^4205 ≤ (13510446207449929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5711 : ℕ)^4205*100000000000000000000^1024 ≤ 13510446207449929^1024*50000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5711 50000 13510446207449929 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5711/50000 : ℝ)) (X := (13510446207449929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (4205/1024 : ℝ) ≤ (32273248015222047/100000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^4205 ≤ (32273248015222047/100000000000000000000 : ℝ)^1024 := by
      have hnat : (353 : ℕ)^4205*100000000000000000000^1024 ≤ 32273248015222047^1024*2500^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 32273248015222047 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (32273248015222047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013510446207449929/50000000000000000000 : ℝ) ≤ (156260280382863/156250000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50013510446207449929/50000000000000000000 : ℝ)^1024 ≤ (156260280382863/156250000000000 : ℝ)^4205 := by
      have hnat : (50013510446207449929 : ℕ)^1024*156250000000000^4205 ≤ 156260280382863^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013510446207449929 50000000000000000000 156260280382863 156250000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156260280382863/156250000000000 : ℝ)) (X := (50013510446207449929/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505722961777833997/12500000000000000000 : ℝ) ≤ (2000222945951521/2000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (12505722961777833997/12500000000000000000 : ℝ)^1024 ≤ (2000222945951521/2000000000000000 : ℝ)^4205 := by
      have hnat : (12505722961777833997 : ℕ)^1024*2000000000000000^4205 ≤ 2000222945951521^4205*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505722961777833997 12500000000000000000 2000222945951521 2000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222945951521/2000000000000000 : ℝ)) (X := (12505722961777833997/12500000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032273248015222047/50000000000000000000 : ℝ) ≤ (5000785757505989/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50032273248015222047/50000000000000000000 : ℝ)^1024 ≤ (5000785757505989/5000000000000000 : ℝ)^4205 := by
      have hnat : (50032273248015222047 : ℕ)^1024*5000000000000000^4205 ≤ 5000785757505989^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032273248015222047 50000000000000000000 5000785757505989 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000785757505989/5000000000000000 : ℝ)) (X := (50032273248015222047/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13510446207449929/100000000000000000000 : ℝ) ≤ ((6742835082979705781/6745000000000000000 : ℝ)+2*(456785254373/269800000000000 : ℝ)*(5711/50000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (6742835082979705781/6745000000000000000 : ℝ)+2*(456785254373/269800000000000 : ℝ)*(5711/50000 : ℝ)=(156260280382863/156250000000000 : ℝ) by norm_num, show 1+2*(13510446207449929/100000000000000000000 : ℝ)=(50013510446207449929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32273248015222047/100000000000000000000 : ℝ)+(13510446207449929/100000000000000000000 : ℝ) ≤ ((6742835082979705781/6745000000000000000 : ℝ)+(456785254373/269800000000000 : ℝ)*((353/2500 : ℝ)+(5711/50000 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (6742835082979705781/6745000000000000000 : ℝ)+(456785254373/269800000000000 : ℝ)*((353/2500 : ℝ)+(5711/50000 : ℝ))=(2000222945951521/2000000000000000 : ℝ) by norm_num, show 1+(32273248015222047/100000000000000000000 : ℝ)+(13510446207449929/100000000000000000000 : ℝ)=(12505722961777833997/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32273248015222047/100000000000000000000 : ℝ) ≤ ((6742835082979705781/6745000000000000000 : ℝ)+2*(456785254373/269800000000000 : ℝ)*(353/2500 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (6742835082979705781/6745000000000000000 : ℝ)+2*(456785254373/269800000000000 : ℝ)*(353/2500 : ℝ)=(5000785757505989/5000000000000000 : ℝ) by norm_num, show 1+2*(32273248015222047/100000000000000000000 : ℝ)=(50032273248015222047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6742835082979705781/6745000000000000000 : ℝ)*(X 1 0+X 2 0)+(456785254373/269800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (6742835082979705781/6745000000000000000 : ℝ)) (alpha := (456785254373/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6742835082979705781/6745000000000000000 : ℝ)*(X 0 1+X 2 1)+(456785254373/269800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (6742835082979705781/6745000000000000000 : ℝ)) (alpha := (456785254373/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6742835082979705781/6745000000000000000 : ℝ)*(X 0 2+X 1 2)+(456785254373/269800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (6742835082979705781/6745000000000000000 : ℝ)) (alpha := (456785254373/269800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131043579/10000000000 : ℝ)*X 0 0+(539186569/1000000000 : ℝ)*X 0 1+(658334503/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534448743/1000000000 : ℝ)*X 1 0+(-43890537/200000000 : ℝ)*X 1 1+(1316668947/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344487331/10000000000 : ℝ)*X 2 0+(1316668969/2500000000 : ℝ)*X 2 1+(-1097263433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354064107/10000000000 : ℝ)*X 0 0+(845893553/2000000000 : ℝ)*X 0 1+(448224787/1000000000 : ℝ)*X 0 2+(4354064107/10000000000 : ℝ)*X 1 0+(845893553/2000000000 : ℝ)*X 1 1+(448224787/1000000000 : ℝ)*X 1 2+(4354064107/10000000000 : ℝ)*X 2 0+(845893553/2000000000 : ℝ)*X 2 1+(448224787/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131048441/10000000000 : ℝ)*X 0 0+(42135939/80000000 : ℝ)*X 0 1+(539154811/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106251939/200000000 : ℝ)*X 1 0+(-2069654599/10000000000 : ℝ)*X 1 1+(5391548099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656298473/5000000000 : ℝ)*X 2 0+(673943513/1250000000 : ℝ)*X 2 1+(-2069654599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272129619/625000000 : ℝ)*X 0 0+(4481608733/10000000000 : ℝ)*X 0 1+(1057527259/2500000000 : ℝ)*X 0 2+(272129619/625000000 : ℝ)*X 1 0+(4481608733/10000000000 : ℝ)*X 1 1+(1057527259/2500000000 : ℝ)*X 1 2+(272129619/625000000 : ℝ)*X 2 0+(4481608733/10000000000 : ℝ)*X 2 1+(1057527259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15264147687643599344408469/4437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (368506457/100000000000000 : ℝ)*(base19) + (70175561/25000000000000 : ℝ)*(base23) + (14087959/100000000000000 : ℝ)*(lower3) + (34072679/100000000000000 : ℝ)*(lower4) + (1051059/20000000000000 : ℝ)*(lower5) + (2985974168953577/50000000000000 : ℝ)*(major0) + (2985974168953577/50000000000000 : ℝ)*(major1) + (2985974168953577/50000000000000 : ℝ)*(major2) + (199697048908677/2500000000000 : ℝ)*(sp0) + (7987881587840623/100000000000000 : ℝ)*(sp1) + (998485134217289/12500000000000 : ℝ)*(sp2) + (989002930607431/25000000000000 : ℝ)*(sp3) + (150476631/25000000000000 : ℝ)*(sp6) + (2882377231/100000000000000 : ℝ)*(sp7) + (791202920961391/20000000000000 : ℝ)*(f.failure) + (199697048908677/2500000000000 : ℝ)*(f.sum) + (4748537228101/355000000000000000000000000 : ℝ)*base66 + (15548291921247177/17750000000000000000000000000000 : ℝ)*base68 + (84052051431997177/17750000000000000000000000000000 : ℝ)*base70 + (388418544603497177/17750000000000000000000000000000 : ℝ)*base72 + (10467340689/88750000000000000000000000 : ℝ)*base74 + (208849111997002823/17750000000000000000000000000000 : ℝ)*base75 + (140030939129997177/17750000000000000000000000000000 : ℝ)*base78 + (278622934213247177/17750000000000000000000000000000 : ℝ)*base80 + (439625836519/355000000000000000000000000 : ℝ)*base81 + (18435873/2000000000000000000000 : ℝ)*base89 + (18435873/2000000000000000000000 : ℝ)*base91 + (18435873/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1697728091776164214747105149/168625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1817371279/100000000000000 : ℝ)*(base19) + (30797357/1562500000000 : ℝ)*(base23) + (25080583/12500000000000 : ℝ)*(upper3) + (73161291/100000000000000 : ℝ)*(lower4) + (52133193/25000000000000 : ℝ)*(upper5) + (6002340036108343/100000000000000 : ℝ)*(major0) + (6002340036108343/100000000000000 : ℝ)*(major1) + (6002340036108343/100000000000000 : ℝ)*(major2) + (12573859627/25000000000000 : ℝ)*(sp1) + (5395915521/10000000000000 : ℝ)*(sp2) + (802853267332891/10000000000000 : ℝ)*(sp4) + (4014240280259561/50000000000000 : ℝ)*(sp5) + (2007119185785713/25000000000000 : ℝ)*(sp6) + (994036765821369/25000000000000 : ℝ)*(sp7) + (994036765821369/25000000000000 : ℝ)*(f.failure) + (802853267332891/10000000000000 : ℝ)*(f.sum) + (115565777995121/13490000000000000000000000000 : ℝ)*base66 + (5679498488343094117/674500000000000000000000000000000 : ℝ)*base68 + (4551395941954094117/674500000000000000000000000000000 : ℝ)*base70 + (9503190077650094117/674500000000000000000000000000000 : ℝ)*base72 + (38549898070761/13490000000000000000000000000 : ℝ)*base74 + (7940456509336905883/674500000000000000000000000000000 : ℝ)*base75 + (4772747665919094117/674500000000000000000000000000000 : ℝ)*base78 + (4135841375334094117/674500000000000000000000000000000 : ℝ)*base80 + (33174576864781/13490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (18924407/2500000000000000000000 : ℝ)*base89 + (18924407/2500000000000000000000 : ℝ)*base91 + (18924407/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1218_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s7_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131059263/10000000000 : ℝ)*x 0 + (1078329351/2000000000 : ℝ)*x 1 + (164590153/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131059263/10000000000 : ℝ)^8411 ≤ (12956770761837/100000000000000 : ℝ)^6363 := by
    have hnat : (2131059263 : ℕ)^8411*100000000000000^6363 ≤ 12956770761837^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131059263 10000000000 12956770761837 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078329351/2000000000 : ℝ)^8411 ≤ (44194994809367/100000000000000 : ℝ)^6363 := by
    have hnat : (1078329351 : ℕ)^8411*100000000000000^6363 ≤ 44194994809367^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078329351 2000000000 44194994809367 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164590153/312500000 : ℝ)^8411 ≤ (10712058601289/25000000000000 : ℝ)^6363 := by
    have hnat : (164590153 : ℕ)^8411*25000000000000^6363 ≤ 10712058601289^6363*312500000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164590153 312500000 10712058601289 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131059263/10000000000 : ℝ), (1078329351/2000000000 : ℝ), (164590153/312500000 : ℝ)] ![(12956770761837/100000000000000 : ℝ), (44194994809367/100000000000000 : ℝ), (10712058601289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131059263/10000000000 : ℝ)|^8411 ≤ (12956770761837/100000000000000 : ℝ)^6363
        have hw : |(-2131059263/10000000000 : ℝ)|=(2131059263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078329351/2000000000 : ℝ)|^8411 ≤ (44194994809367/100000000000000 : ℝ)^6363
        have hw : |(1078329351/2000000000 : ℝ)|=(1078329351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164590153/312500000 : ℝ)|^8411 ≤ (10712058601289/25000000000000 : ℝ)^6363
        have hw : |(164590153/312500000 : ℝ)|=(164590153/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336108157/2500000000 : ℝ)*x 0 + (-2194322111/10000000000 : ℝ)*x 1 + (526688531/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336108157/2500000000 : ℝ)^8411 ≤ (43684142159427/100000000000000 : ℝ)^6363 := by
    have hnat : (1336108157 : ℕ)^8411*100000000000000^6363 ≤ 43684142159427^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336108157 2500000000 43684142159427 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194322111/10000000000 : ℝ)^8411 ≤ (6733809480259/50000000000000 : ℝ)^6363 := by
    have hnat : (2194322111 : ℕ)^8411*50000000000000^6363 ≤ 6733809480259^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194322111 10000000000 6733809480259 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526688531/1000000000 : ℝ)^8411 ≤ (21424119428629/50000000000000 : ℝ)^6363 := by
    have hnat : (526688531 : ℕ)^8411*50000000000000^6363 ≤ 21424119428629^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526688531 1000000000 21424119428629 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336108157/2500000000 : ℝ), (-2194322111/10000000000 : ℝ), (526688531/1000000000 : ℝ)] ![(43684142159427/100000000000000 : ℝ), (6733809480259/50000000000000 : ℝ), (21424119428629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336108157/2500000000 : ℝ)|^8411 ≤ (43684142159427/100000000000000 : ℝ)^6363
        have hw : |(1336108157/2500000000 : ℝ)|=(1336108157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194322111/10000000000 : ℝ)|^8411 ≤ (6733809480259/50000000000000 : ℝ)^6363
        have hw : |(-2194322111/10000000000 : ℝ)|=(2194322111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526688531/1000000000 : ℝ)|^8411 ≤ (21424119428629/50000000000000 : ℝ)^6363
        have hw : |(526688531/1000000000 : ℝ)|=(526688531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336108207/2500000000 : ℝ)*x 0 + (5266885009/10000000000 : ℝ)*x 1 + (-548580561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336108207/2500000000 : ℝ)^8411 ≤ (43684144320343/100000000000000 : ℝ)^6363 := by
    have hnat : (1336108207 : ℕ)^8411*100000000000000^6363 ≤ 43684144320343^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336108207 2500000000 43684144320343 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266885009/10000000000 : ℝ)^8411 ≤ (42848235620343/100000000000000 : ℝ)^6363 := by
    have hnat : (5266885009 : ℕ)^8411*100000000000000^6363 ≤ 42848235620343^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266885009 10000000000 42848235620343 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548580561/2500000000 : ℝ)^8411 ≤ (6733810019767/50000000000000 : ℝ)^6363 := by
    have hnat : (548580561 : ℕ)^8411*50000000000000^6363 ≤ 6733810019767^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548580561 2500000000 6733810019767 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336108207/2500000000 : ℝ), (5266885009/10000000000 : ℝ), (-548580561/2500000000 : ℝ)] ![(43684144320343/100000000000000 : ℝ), (42848235620343/100000000000000 : ℝ), (6733810019767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336108207/2500000000 : ℝ)|^8411 ≤ (43684144320343/100000000000000 : ℝ)^6363
        have hw : |(1336108207/2500000000 : ℝ)|=(1336108207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266885009/10000000000 : ℝ)|^8411 ≤ (42848235620343/100000000000000 : ℝ)^6363
        have hw : |(5266885009/10000000000 : ℝ)|=(5266885009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548580561/2500000000 : ℝ)|^8411 ≤ (6733810019767/50000000000000 : ℝ)^6363
        have hw : |(-548580561/2500000000 : ℝ)|=(548580561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354075863/10000000000 : ℝ)*x 0 + (1057474399/2500000000 : ℝ)*x 1 + (896362867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354075863/10000000000 : ℝ)^8411 ≤ (33317375384303/100000000000000 : ℝ)^6363 := by
    have hnat : (4354075863 : ℕ)^8411*100000000000000^6363 ≤ 33317375384303^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354075863 10000000000 33317375384303 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057474399/2500000000 : ℝ)^8411 ≤ (32067130336923/100000000000000 : ℝ)^6363 := by
    have hnat : (1057474399 : ℕ)^8411*100000000000000^6363 ≤ 32067130336923^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057474399 2500000000 32067130336923 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896362867/2000000000 : ℝ)^8411 ≤ (34615494263899/100000000000000 : ℝ)^6363 := by
    have hnat : (896362867 : ℕ)^8411*100000000000000^6363 ≤ 34615494263899^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896362867 2000000000 34615494263899 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354075863/10000000000 : ℝ), (1057474399/2500000000 : ℝ), (896362867/2000000000 : ℝ)] ![(33317375384303/100000000000000 : ℝ), (32067130336923/100000000000000 : ℝ), (34615494263899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354075863/10000000000 : ℝ)|^8411 ≤ (33317375384303/100000000000000 : ℝ)^6363
        have hw : |(4354075863/10000000000 : ℝ)|=(4354075863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057474399/2500000000 : ℝ)|^8411 ≤ (32067130336923/100000000000000 : ℝ)^6363
        have hw : |(1057474399/2500000000 : ℝ)|=(1057474399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896362867/2000000000 : ℝ)|^8411 ≤ (34615494263899/100000000000000 : ℝ)^6363
        have hw : |(896362867/2000000000 : ℝ)|=(896362867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-426212813/2000000000 : ℝ)*x 0 + (210687969/400000000 : ℝ)*x 1 + (5391331219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426212813/2000000000 : ℝ)^8411 ≤ (6478404677451/50000000000000 : ℝ)^6363 := by
    have hnat : (426212813 : ℕ)^8411*50000000000000^6363 ≤ 6478404677451^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426212813 2000000000 6478404677451 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210687969/400000000 : ℝ)^8411 ≤ (42851614691069/100000000000000 : ℝ)^6363 := by
    have hnat : (210687969 : ℕ)^8411*100000000000000^6363 ≤ 42851614691069^6363*400000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210687969 400000000 42851614691069 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391331219/10000000000 : ℝ)^8411 ≤ (22095787971241/50000000000000 : ℝ)^6363 := by
    have hnat : (5391331219 : ℕ)^8411*50000000000000^6363 ≤ 22095787971241^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391331219 10000000000 22095787971241 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426212813/2000000000 : ℝ), (210687969/400000000 : ℝ), (5391331219/10000000000 : ℝ)] ![(6478404677451/50000000000000 : ℝ), (42851614691069/100000000000000 : ℝ), (22095787971241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426212813/2000000000 : ℝ)|^8411 ≤ (6478404677451/50000000000000 : ℝ)^6363
        have hw : |(-426212813/2000000000 : ℝ)|=(426212813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210687969/400000000 : ℝ)|^8411 ≤ (42851614691069/100000000000000 : ℝ)^6363
        have hw : |(210687969/400000000 : ℝ)|=(210687969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391331219/10000000000 : ℝ)|^8411 ≤ (22095787971241/50000000000000 : ℝ)^6363
        have hw : |(5391331219/10000000000 : ℝ)|=(5391331219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651349/10000000000 : ℝ)*x 0 + (-2069876069/10000000000 : ℝ)*x 1 + (5391331219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651349/10000000000 : ℝ)^8411 ≤ (43341087825583/100000000000000 : ℝ)^6363 := by
    have hnat : (5312651349 : ℕ)^8411*100000000000000^6363 ≤ 43341087825583^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651349 10000000000 43341087825583 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069876069/10000000000 : ℝ)^8411 ≤ (3116834054527/25000000000000 : ℝ)^6363 := by
    have hnat : (2069876069 : ℕ)^8411*25000000000000^6363 ≤ 3116834054527^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069876069 10000000000 3116834054527 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391331219/10000000000 : ℝ)^8411 ≤ (22095787971241/50000000000000 : ℝ)^6363 := by
    have hnat : (5391331219 : ℕ)^8411*50000000000000^6363 ≤ 22095787971241^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391331219 10000000000 22095787971241 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651349/10000000000 : ℝ), (-2069876069/10000000000 : ℝ), (5391331219/10000000000 : ℝ)] ![(43341087825583/100000000000000 : ℝ), (3116834054527/25000000000000 : ℝ), (22095787971241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651349/10000000000 : ℝ)|^8411 ≤ (43341087825583/100000000000000 : ℝ)^6363
        have hw : |(5312651349/10000000000 : ℝ)|=(5312651349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069876069/10000000000 : ℝ)|^8411 ≤ (3116834054527/25000000000000 : ℝ)^6363
        have hw : |(-2069876069/10000000000 : ℝ)|=(2069876069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391331219/10000000000 : ℝ)|^8411 ≤ (22095787971241/50000000000000 : ℝ)^6363
        have hw : |(5391331219/10000000000 : ℝ)|=(5391331219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651349/10000000000 : ℝ)*x 0 + (2695665609/5000000000 : ℝ)*x 1 + (-2069876069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651349/10000000000 : ℝ)^8411 ≤ (43341087825583/100000000000000 : ℝ)^6363 := by
    have hnat : (5312651349 : ℕ)^8411*100000000000000^6363 ≤ 43341087825583^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651349 10000000000 43341087825583 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695665609/5000000000 : ℝ)^8411 ≤ (44191575931647/100000000000000 : ℝ)^6363 := by
    have hnat : (2695665609 : ℕ)^8411*100000000000000^6363 ≤ 44191575931647^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695665609 5000000000 44191575931647 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069876069/10000000000 : ℝ)^8411 ≤ (3116834054527/25000000000000 : ℝ)^6363 := by
    have hnat : (2069876069 : ℕ)^8411*25000000000000^6363 ≤ 3116834054527^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069876069 10000000000 3116834054527 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651349/10000000000 : ℝ), (2695665609/5000000000 : ℝ), (-2069876069/10000000000 : ℝ)] ![(43341087825583/100000000000000 : ℝ), (44191575931647/100000000000000 : ℝ), (3116834054527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651349/10000000000 : ℝ)|^8411 ≤ (43341087825583/100000000000000 : ℝ)^6363
        have hw : |(5312651349/10000000000 : ℝ)|=(5312651349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695665609/5000000000 : ℝ)|^8411 ≤ (44191575931647/100000000000000 : ℝ)^6363
        have hw : |(2695665609/5000000000 : ℝ)|=(2695665609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069876069/10000000000 : ℝ)|^8411 ≤ (3116834054527/25000000000000 : ℝ)^6363
        have hw : |(-2069876069/10000000000 : ℝ)|=(2069876069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s7_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870816929/2000000000 : ℝ)*x 0 + (896235907/2000000000 : ℝ)*x 1 + (4230535433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870816929/2000000000 : ℝ)^8411 ≤ (832936605329/2500000000000 : ℝ)^6363 := by
    have hnat : (870816929 : ℕ)^8411*2500000000000^6363 ≤ 832936605329^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870816929 2000000000 832936605329 2500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896235907/2000000000 : ℝ)^8411 ≤ (34609013452189/100000000000000 : ℝ)^6363 := by
    have hnat : (896235907 : ℕ)^8411*100000000000000^6363 ≤ 34609013452189^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896235907 2000000000 34609013452189 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230535433/10000000000 : ℝ)^8411 ≤ (32073522328593/100000000000000 : ℝ)^6363 := by
    have hnat : (4230535433 : ℕ)^8411*100000000000000^6363 ≤ 32073522328593^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230535433 10000000000 32073522328593 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870816929/2000000000 : ℝ), (896235907/2000000000 : ℝ), (4230535433/10000000000 : ℝ)] ![(832936605329/2500000000000 : ℝ), (34609013452189/100000000000000 : ℝ), (32073522328593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870816929/2000000000 : ℝ)|^8411 ≤ (832936605329/2500000000000 : ℝ)^6363
        have hw : |(870816929/2000000000 : ℝ)|=(870816929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896235907/2000000000 : ℝ)|^8411 ≤ (34609013452189/100000000000000 : ℝ)^6363
        have hw : |(896235907/2000000000 : ℝ)|=(896235907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230535433/10000000000 : ℝ)|^8411 ≤ (32073522328593/100000000000000 : ℝ)^6363
        have hw : |(4230535433/10000000000 : ℝ)|=(4230535433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11449/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2289/20000 : ℝ) ^ (4205/1024 : ℝ) ≤ (13622513669615157/100000000000000000000 : ℝ) := by
    have hpowers : (2289/20000 : ℝ)^4205 ≤ (13622513669615157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2289 : ℕ)^4205*100000000000000000000^1024 ≤ 13622513669615157^1024*20000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 20000 13622513669615157 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/20000 : ℝ)) (X := (13622513669615157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (4205/1024 : ℝ) ≤ (32057918806639259/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^4205 ≤ (32057918806639259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14097 : ℕ)^4205*100000000000000000000^1024 ≤ 32057918806639259^1024*100000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 32057918806639259 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (32057918806639259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013622513669615157/50000000000000000000 : ℝ) ≤ (5000331700754169/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50013622513669615157/50000000000000000000 : ℝ)^1024 ≤ (5000331700754169/5000000000000000 : ℝ)^4205 := by
      have hnat : (50013622513669615157 : ℕ)^1024*5000000000000000^4205 ≤ 5000331700754169^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013622513669615157 50000000000000000000 5000331700754169 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331700754169/5000000000000000 : ℝ)) (X := (50013622513669615157/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252855027029765901/6250000000000000000 : ℝ) ≤ (5000556108000541/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (6252855027029765901/6250000000000000000 : ℝ)^1024 ≤ (5000556108000541/5000000000000000 : ℝ)^4205 := by
      have hnat : (6252855027029765901 : ℕ)^1024*5000000000000000^4205 ≤ 5000556108000541^4205*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252855027029765901 6250000000000000000 5000556108000541 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000556108000541/5000000000000000 : ℝ)) (X := (6252855027029765901/6250000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032057918806639259/50000000000000000000 : ℝ) ≤ (5000780515246913/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50032057918806639259/50000000000000000000 : ℝ)^1024 ≤ (5000780515246913/5000000000000000 : ℝ)^4205 := by
      have hnat : (50032057918806639259 : ℕ)^1024*5000000000000000^4205 ≤ 5000780515246913^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032057918806639259 50000000000000000000 5000780515246913 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000780515246913/5000000000000000 : ℝ)) (X := (50032057918806639259/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13622513669615157/100000000000000000000 : ℝ) ≤ ((1104645249044216759/1105000000000000000 : ℝ)+2*(56101811593/33150000000000 : ℝ)*(2289/20000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1104645249044216759/1105000000000000000 : ℝ)+2*(56101811593/33150000000000 : ℝ)*(2289/20000 : ℝ)=(5000331700754169/5000000000000000 : ℝ) by norm_num, show 1+2*(13622513669615157/100000000000000000000 : ℝ)=(50013622513669615157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32057918806639259/100000000000000000000 : ℝ)+(13622513669615157/100000000000000000000 : ℝ) ≤ ((1104645249044216759/1105000000000000000 : ℝ)+(56101811593/33150000000000 : ℝ)*((14097/100000 : ℝ)+(2289/20000 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (1104645249044216759/1105000000000000000 : ℝ)+(56101811593/33150000000000 : ℝ)*((14097/100000 : ℝ)+(2289/20000 : ℝ))=(5000556108000541/5000000000000000 : ℝ) by norm_num, show 1+(32057918806639259/100000000000000000000 : ℝ)+(13622513669615157/100000000000000000000 : ℝ)=(6252855027029765901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32057918806639259/100000000000000000000 : ℝ) ≤ ((1104645249044216759/1105000000000000000 : ℝ)+2*(56101811593/33150000000000 : ℝ)*(14097/100000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1104645249044216759/1105000000000000000 : ℝ)+2*(56101811593/33150000000000 : ℝ)*(14097/100000 : ℝ)=(5000780515246913/5000000000000000 : ℝ) by norm_num, show 1+2*(32057918806639259/100000000000000000000 : ℝ)=(50032057918806639259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1104645249044216759/1105000000000000000 : ℝ)*(X 1 0+X 2 0)+(56101811593/33150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1104645249044216759/1105000000000000000 : ℝ)) (alpha := (56101811593/33150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1104645249044216759/1105000000000000000 : ℝ)*(X 0 1+X 2 1)+(56101811593/33150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1104645249044216759/1105000000000000000 : ℝ)) (alpha := (56101811593/33150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1104645249044216759/1105000000000000000 : ℝ)*(X 0 2+X 1 2)+(56101811593/33150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (1104645249044216759/1105000000000000000 : ℝ)) (alpha := (56101811593/33150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131059263/10000000000 : ℝ)*X 0 0+(1078329351/2000000000 : ℝ)*X 0 1+(164590153/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336108157/2500000000 : ℝ)*X 1 0+(-2194322111/10000000000 : ℝ)*X 1 1+(526688531/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336108207/2500000000 : ℝ)*X 2 0+(5266885009/10000000000 : ℝ)*X 2 1+(-548580561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354075863/10000000000 : ℝ)*X 0 0+(1057474399/2500000000 : ℝ)*X 0 1+(896362867/2000000000 : ℝ)*X 0 2+(4354075863/10000000000 : ℝ)*X 1 0+(1057474399/2500000000 : ℝ)*X 1 1+(896362867/2000000000 : ℝ)*X 1 2+(4354075863/10000000000 : ℝ)*X 2 0+(1057474399/2500000000 : ℝ)*X 2 1+(896362867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-426212813/2000000000 : ℝ)*X 0 0+(210687969/400000000 : ℝ)*X 0 1+(5391331219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312651349/10000000000 : ℝ)*X 1 0+(-2069876069/10000000000 : ℝ)*X 1 1+(5391331219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312651349/10000000000 : ℝ)*X 2 0+(2695665609/5000000000 : ℝ)*X 2 1+(-2069876069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870816929/2000000000 : ℝ)*X 0 0+(896235907/2000000000 : ℝ)*X 0 1+(4230535433/10000000000 : ℝ)*X 0 2+(870816929/2000000000 : ℝ)*X 1 0+(896235907/2000000000 : ℝ)*X 1 1+(4230535433/10000000000 : ℝ)*X 1 2+(870816929/2000000000 : ℝ)*X 2 0+(896235907/2000000000 : ℝ)*X 2 1+(4230535433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3429730934516036929989/552500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1512952601/100000000000000 : ℝ)*(base19) + (1380855929/100000000000000 : ℝ)*(base23) + (318926901/100000000000000 : ℝ)*(lower2) + (480715701/100000000000000 : ℝ)*(upper3) + (343833/390625000000 : ℝ)*(lower4) + (2996251544931397/50000000000000 : ℝ)*(major0) + (2996251544931397/50000000000000 : ℝ)*(major1) + (2996251544931397/50000000000000 : ℝ)*(major2) + (8015329646221181/100000000000000 : ℝ)*(sp0) + (8015373712650749/100000000000000 : ℝ)*(sp1) + (8015373844747421/100000000000000 : ℝ)*(sp2) + (3969591181605749/100000000000000 : ℝ)*(sp3) + (45579382169/100000000000000 : ℝ)*(sp4) + (39565594559/100000000000000 : ℝ)*(sp7) + (992407686800077/25000000000000 : ℝ)*(f.failure) + (160307504512067/2000000000000 : ℝ)*(f.sum) + (3486268514087/1657500000000000000000000000 : ℝ)*base65 + (237310373896603031/165750000000000000000000000000000 : ℝ)*base68 + (176906267146603031/165750000000000000000000000000000 : ℝ)*base70 + (480344832504646969/165750000000000000000000000000000 : ℝ)*base71 + (1670076188867/1657500000000000000000000000 : ℝ)*base73 + (1642781606146969/165750000000000000000000000000000 : ℝ)*base75 + (10195253202646969/165750000000000000000000000000000 : ℝ)*base77 + (1889800598213353031/165750000000000000000000000000000 : ℝ)*base80 + (2955351566357/1657500000000000000000000000 : ℝ)*base81 + (5779869/2500000000000000000000 : ℝ)*base90 + (5779869/2500000000000000000000 : ℝ)*base92 + (5779869/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3429033621092478699853/552500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1122258169/100000000000000 : ℝ)*(base19) + (1218845793/100000000000000 : ℝ)*(base23) + (24954967/20000000000000 : ℝ)*(upper3) + (4407279/10000000000000 : ℝ)*(lower4) + (63525103/50000000000000 : ℝ)*(upper5) + (6022830209962561/100000000000000 : ℝ)*(major0) + (6022830209962561/100000000000000 : ℝ)*(major1) + (6022830209962561/100000000000000 : ℝ)*(major2) + (15767363697/50000000000000 : ℝ)*(sp1) + (33812851649/100000000000000 : ℝ)*(sp2) + (8055939786020549/100000000000000 : ℝ)*(sp4) + (4027953564517493/50000000000000 : ℝ)*(sp5) + (8055904754323107/100000000000000 : ℝ)*(sp6) + (997430106756177/25000000000000 : ℝ)*(sp7) + (997430106756177/25000000000000 : ℝ)*(f.failure) + (8055939786020549/100000000000000 : ℝ)*(f.sum) + (10467274532779/3315000000000000000000000000 : ℝ)*base66 + (370952307236079397/331500000000000000000000000000000 : ℝ)*base67 + (2035794873198920603/331500000000000000000000000000000 : ℝ)*base70 + (337076023554579397/331500000000000000000000000000000 : ℝ)*base71 + (8580552490217/1657500000000000000000000000 : ℝ)*base74 + (9354980337653420603/331500000000000000000000000000000 : ℝ)*base76 + (2268114187031079397/331500000000000000000000000000000 : ℝ)*base77 + (5383890889086920603/331500000000000000000000000000000 : ℝ)*base80 + (5438974439471/3315000000000000000000000000 : ℝ)*base81 + (7841569/2500000000000000000000 : ℝ)*base90 + (7841569/2500000000000000000000 : ℝ)*base92 + (7841569/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s8_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131065451/10000000000 : ℝ)*x 0 + (2695801373/5000000000 : ℝ)*x 1 + (2633462307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131065451/10000000000 : ℝ)^8411 ≤ (6478410247007/50000000000000 : ℝ)^6363 := by
    have hnat : (2131065451 : ℕ)^8411*50000000000000^6363 ≤ 6478410247007^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131065451 10000000000 6478410247007 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695801373/5000000000 : ℝ)^8411 ≤ (27621573727/62500000000 : ℝ)^6363 := by
    have hnat : (2695801373 : ℕ)^8411*62500000000^6363 ≤ 27621573727^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695801373 5000000000 27621573727 62500000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633462307/5000000000 : ℝ)^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363 := by
    have hnat : (2633462307 : ℕ)^8411*50000000000000^6363 ≤ 21424330763957^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633462307 5000000000 21424330763957 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131065451/10000000000 : ℝ), (2695801373/5000000000 : ℝ), (2633462307/5000000000 : ℝ)] ![(6478410247007/50000000000000 : ℝ), (27621573727/62500000000 : ℝ), (21424330763957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131065451/10000000000 : ℝ)|^8411 ≤ (6478410247007/50000000000000 : ℝ)^6363
        have hw : |(-2131065451/10000000000 : ℝ)|=(2131065451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695801373/5000000000 : ℝ)|^8411 ≤ (27621573727/62500000000 : ℝ)^6363
        have hw : |(2695801373/5000000000 : ℝ)|=(2695801373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633462307/5000000000 : ℝ)|^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363
        have hw : |(2633462307/5000000000 : ℝ)|=(2633462307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344421017/10000000000 : ℝ)*x 0 + (-2194285477/10000000000 : ℝ)*x 1 + (2633462307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344421017/10000000000 : ℝ)^8411 ≤ (8736803341497/20000000000000 : ℝ)^6363 := by
    have hnat : (5344421017 : ℕ)^8411*20000000000000^6363 ≤ 8736803341497^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344421017 10000000000 8736803341497 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194285477/10000000000 : ℝ)^8411 ≤ (13467321753319/100000000000000 : ℝ)^6363 := by
    have hnat : (2194285477 : ℕ)^8411*100000000000000^6363 ≤ 13467321753319^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194285477 10000000000 13467321753319 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633462307/5000000000 : ℝ)^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363 := by
    have hnat : (2633462307 : ℕ)^8411*50000000000000^6363 ≤ 21424330763957^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633462307 5000000000 21424330763957 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344421017/10000000000 : ℝ), (-2194285477/10000000000 : ℝ), (2633462307/5000000000 : ℝ)] ![(8736803341497/20000000000000 : ℝ), (13467321753319/100000000000000 : ℝ), (21424330763957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344421017/10000000000 : ℝ)|^8411 ≤ (8736803341497/20000000000000 : ℝ)^6363
        have hw : |(5344421017/10000000000 : ℝ)|=(5344421017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194285477/10000000000 : ℝ)|^8411 ≤ (13467321753319/100000000000000 : ℝ)^6363
        have hw : |(-2194285477/10000000000 : ℝ)|=(2194285477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633462307/5000000000 : ℝ)|^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363
        have hw : |(2633462307/5000000000 : ℝ)|=(2633462307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344421017/10000000000 : ℝ)*x 0 + (2633462307/5000000000 : ℝ)*x 1 + (-2194285477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344421017/10000000000 : ℝ)^8411 ≤ (8736803341497/20000000000000 : ℝ)^6363 := by
    have hnat : (5344421017 : ℕ)^8411*20000000000000^6363 ≤ 8736803341497^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344421017 10000000000 8736803341497 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633462307/5000000000 : ℝ)^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363 := by
    have hnat : (2633462307 : ℕ)^8411*50000000000000^6363 ≤ 21424330763957^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633462307 5000000000 21424330763957 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194285477/10000000000 : ℝ)^8411 ≤ (13467321753319/100000000000000 : ℝ)^6363 := by
    have hnat : (2194285477 : ℕ)^8411*100000000000000^6363 ≤ 13467321753319^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194285477 10000000000 13467321753319 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344421017/10000000000 : ℝ), (2633462307/5000000000 : ℝ), (-2194285477/10000000000 : ℝ)] ![(8736803341497/20000000000000 : ℝ), (21424330763957/50000000000000 : ℝ), (13467321753319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344421017/10000000000 : ℝ)|^8411 ≤ (8736803341497/20000000000000 : ℝ)^6363
        have hw : |(5344421017/10000000000 : ℝ)|=(5344421017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633462307/5000000000 : ℝ)|^8411 ≤ (21424330763957/50000000000000 : ℝ)^6363
        have hw : |(2633462307/5000000000 : ℝ)|=(2633462307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194285477/10000000000 : ℝ)|^8411 ≤ (13467321753319/100000000000000 : ℝ)^6363
        have hw : |(-2194285477/10000000000 : ℝ)|=(2194285477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354077251/10000000000 : ℝ)*x 0 + (4229982637/10000000000 : ℝ)*x 1 + (4481729487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354077251/10000000000 : ℝ)^8411 ≤ (33317389423749/100000000000000 : ℝ)^6363 := by
    have hnat : (4354077251 : ℕ)^8411*100000000000000^6363 ≤ 33317389423749^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354077251 10000000000 33317389423749 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229982637/10000000000 : ℝ)^8411 ≤ (32067982545139/100000000000000 : ℝ)^6363 := by
    have hnat : (4229982637 : ℕ)^8411*100000000000000^6363 ≤ 32067982545139^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229982637 10000000000 32067982545139 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481729487/10000000000 : ℝ)^8411 ≤ (34614628015047/100000000000000 : ℝ)^6363 := by
    have hnat : (4481729487 : ℕ)^8411*100000000000000^6363 ≤ 34614628015047^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481729487 10000000000 34614628015047 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354077251/10000000000 : ℝ), (4229982637/10000000000 : ℝ), (4481729487/10000000000 : ℝ)] ![(33317389423749/100000000000000 : ℝ), (32067982545139/100000000000000 : ℝ), (34614628015047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354077251/10000000000 : ℝ)|^8411 ≤ (33317389423749/100000000000000 : ℝ)^6363
        have hw : |(4354077251/10000000000 : ℝ)|=(4354077251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229982637/10000000000 : ℝ)|^8411 ≤ (32067982545139/100000000000000 : ℝ)^6363
        have hw : |(4229982637/10000000000 : ℝ)|=(4229982637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481729487/10000000000 : ℝ)|^8411 ≤ (34614628015047/100000000000000 : ℝ)^6363
        have hw : |(4481729487/10000000000 : ℝ)|=(4481729487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065535071/5000000000 : ℝ)*x 0 + (5267238549/10000000000 : ℝ)*x 1 + (5391287681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065535071/5000000000 : ℝ)^8411 ≤ (12956858195021/100000000000000 : ℝ)^6363 := by
    have hnat : (1065535071 : ℕ)^8411*100000000000000^6363 ≤ 12956858195021^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065535071 5000000000 12956858195021 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267238549/10000000000 : ℝ)^8411 ≤ (8570407516983/20000000000000 : ℝ)^6363 := by
    have hnat : (5267238549 : ℕ)^8411*20000000000000^6363 ≤ 8570407516983^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267238549 10000000000 8570407516983 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391287681/10000000000 : ℝ)^8411 ≤ (11047776052143/25000000000000 : ℝ)^6363 := by
    have hnat : (5391287681 : ℕ)^8411*25000000000000^6363 ≤ 11047776052143^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391287681 10000000000 11047776052143 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065535071/5000000000 : ℝ), (5267238549/10000000000 : ℝ), (5391287681/10000000000 : ℝ)] ![(12956858195021/100000000000000 : ℝ), (8570407516983/20000000000000 : ℝ), (11047776052143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065535071/5000000000 : ℝ)|^8411 ≤ (12956858195021/100000000000000 : ℝ)^6363
        have hw : |(-1065535071/5000000000 : ℝ)|=(1065535071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267238549/10000000000 : ℝ)|^8411 ≤ (8570407516983/20000000000000 : ℝ)^6363
        have hw : |(5267238549/10000000000 : ℝ)|=(5267238549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391287681/10000000000 : ℝ)|^8411 ≤ (11047776052143/25000000000000 : ℝ)^6363
        have hw : |(5391287681/10000000000 : ℝ)|=(5391287681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656330417/5000000000 : ℝ)*x 0 + (-2069922453/10000000000 : ℝ)*x 1 + (2695643847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656330417/5000000000 : ℝ)^8411 ≤ (8668238022103/20000000000000 : ℝ)^6363 := by
    have hnat : (2656330417 : ℕ)^8411*20000000000000^6363 ≤ 8668238022103^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656330417 5000000000 8668238022103 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069922453/10000000000 : ℝ)^8411 ≤ (623385276139/5000000000000 : ℝ)^6363 := by
    have hnat : (2069922453 : ℕ)^8411*5000000000000^6363 ≤ 623385276139^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069922453 10000000000 623385276139 5000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695643847/5000000000 : ℝ)^8411 ≤ (44191104349427/100000000000000 : ℝ)^6363 := by
    have hnat : (2695643847 : ℕ)^8411*100000000000000^6363 ≤ 44191104349427^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695643847 5000000000 44191104349427 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656330417/5000000000 : ℝ), (-2069922453/10000000000 : ℝ), (2695643847/5000000000 : ℝ)] ![(8668238022103/20000000000000 : ℝ), (623385276139/5000000000000 : ℝ), (44191104349427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656330417/5000000000 : ℝ)|^8411 ≤ (8668238022103/20000000000000 : ℝ)^6363
        have hw : |(2656330417/5000000000 : ℝ)|=(2656330417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069922453/10000000000 : ℝ)|^8411 ≤ (623385276139/5000000000000 : ℝ)^6363
        have hw : |(-2069922453/10000000000 : ℝ)|=(2069922453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695643847/5000000000 : ℝ)|^8411 ≤ (44191104349427/100000000000000 : ℝ)^6363
        have hw : |(2695643847/5000000000 : ℝ)|=(2695643847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062532161/2000000000 : ℝ)*x 0 + (1347821939/2500000000 : ℝ)*x 1 + (-2069922407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062532161/2000000000 : ℝ)^8411 ≤ (43341189797783/100000000000000 : ℝ)^6363 := by
    have hnat : (1062532161 : ℕ)^8411*100000000000000^6363 ≤ 43341189797783^6363*2000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062532161 2000000000 43341189797783 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347821939/2500000000 : ℝ)^8411 ≤ (11047776255299/25000000000000 : ℝ)^6363 := by
    have hnat : (1347821939 : ℕ)^8411*25000000000000^6363 ≤ 11047776255299^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347821939 2500000000 11047776255299 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069922407/10000000000 : ℝ)^8411 ≤ (3116926289133/25000000000000 : ℝ)^6363 := by
    have hnat : (2069922407 : ℕ)^8411*25000000000000^6363 ≤ 3116926289133^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069922407 10000000000 3116926289133 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062532161/2000000000 : ℝ), (1347821939/2500000000 : ℝ), (-2069922407/10000000000 : ℝ)] ![(43341189797783/100000000000000 : ℝ), (11047776255299/25000000000000 : ℝ), (3116926289133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062532161/2000000000 : ℝ)|^8411 ≤ (43341189797783/100000000000000 : ℝ)^6363
        have hw : |(1062532161/2000000000 : ℝ)|=(1062532161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347821939/2500000000 : ℝ)|^8411 ≤ (11047776255299/25000000000000 : ℝ)^6363
        have hw : |(1347821939/2500000000 : ℝ)|=(1347821939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069922407/10000000000 : ℝ)|^8411 ≤ (3116926289133/25000000000000 : ℝ)^6363
        have hw : |(-2069922407/10000000000 : ℝ)|=(2069922407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s8_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354086729/10000000000 : ℝ)*x 0 + (1120273909/2500000000 : ℝ)*x 1 + (4230618797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354086729/10000000000 : ℝ)^8411 ≤ (16658742646287/50000000000000 : ℝ)^6363 := by
    have hnat : (4354086729 : ℕ)^8411*50000000000000^6363 ≤ 16658742646287^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354086729 10000000000 16658742646287 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120273909/2500000000 : ℝ)^8411 ≤ (17304078465549/50000000000000 : ℝ)^6363 := by
    have hnat : (1120273909 : ℕ)^8411*50000000000000^6363 ≤ 17304078465549^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120273909 2500000000 17304078465549 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230618797/10000000000 : ℝ)^8411 ≤ (16037178885919/50000000000000 : ℝ)^6363 := by
    have hnat : (4230618797 : ℕ)^8411*50000000000000^6363 ≤ 16037178885919^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230618797 10000000000 16037178885919 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354086729/10000000000 : ℝ), (1120273909/2500000000 : ℝ), (4230618797/10000000000 : ℝ)] ![(16658742646287/50000000000000 : ℝ), (17304078465549/50000000000000 : ℝ), (16037178885919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354086729/10000000000 : ℝ)|^8411 ≤ (16658742646287/50000000000000 : ℝ)^6363
        have hw : |(4354086729/10000000000 : ℝ)|=(4354086729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120273909/2500000000 : ℝ)|^8411 ≤ (17304078465549/50000000000000 : ℝ)^6363
        have hw : |(1120273909/2500000000 : ℝ)|=(1120273909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230618797/10000000000 : ℝ)|^8411 ≤ (16037178885919/50000000000000 : ℝ)^6363
        have hw : |(4230618797/10000000000 : ℝ)|=(4230618797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (229/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14091/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11449/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11449/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11449/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11449/100000 : ℝ) ^ (4205/1024 : ℝ) ≤ (6821037609260717/50000000000000000000 : ℝ) := by
    have hpowers : (11449/100000 : ℝ)^4205 ≤ (6821037609260717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11449 : ℕ)^4205*50000000000000000000^1024 ≤ 6821037609260717^1024*100000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11449 100000 6821037609260717 50000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11449/100000 : ℝ)) (X := (6821037609260717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (4205/1024 : ℝ) ≤ (32011252287155443/100000000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^4205 ≤ (32011252287155443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3523 : ℕ)^4205*100000000000000000000^1024 ≤ 32011252287155443^1024*25000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 32011252287155443 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (32011252287155443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006821037609260717/25000000000000000000 : ℝ) ≤ (5000332177018037/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (25006821037609260717/25000000000000000000 : ℝ)^1024 ≤ (5000332177018037/5000000000000000 : ℝ)^4205 := by
      have hnat : (25006821037609260717 : ℕ)^1024*5000000000000000^4205 ≤ 5000332177018037^4205*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006821037609260717 25000000000000000000 5000332177018037 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000332177018037/5000000000000000 : ℝ)) (X := (25006821037609260717/25000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045653327505676877/100000000000000000000 : ℝ) ≤ (10001111556169803/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (100045653327505676877/100000000000000000000 : ℝ)^1024 ≤ (10001111556169803/10000000000000000 : ℝ)^4205 := by
      have hnat : (100045653327505676877 : ℕ)^1024*10000000000000000^4205 ≤ 10001111556169803^4205*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045653327505676877 100000000000000000000 10001111556169803 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111556169803/10000000000000000 : ℝ)) (X := (100045653327505676877/100000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032011252287155443/50000000000000000000 : ℝ) ≤ (2500389689575883/2500000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50032011252287155443/50000000000000000000 : ℝ)^1024 ≤ (2500389689575883/2500000000000000 : ℝ)^4205 := by
      have hnat : (50032011252287155443 : ℕ)^1024*2500000000000000^4205 ≤ 2500389689575883^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032011252287155443 50000000000000000000 2500389689575883 2500000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500389689575883/2500000000000000 : ℝ)) (X := (50032011252287155443/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6821037609260717/50000000000000000000 : ℝ) ≤ ((1321075792662960847/1321500000000000000 : ℝ)+2*(447202133729/264300000000000 : ℝ)*(11449/100000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1321075792662960847/1321500000000000000 : ℝ)+2*(447202133729/264300000000000 : ℝ)*(11449/100000 : ℝ)=(5000332177018037/5000000000000000 : ℝ) by norm_num, show 1+2*(6821037609260717/50000000000000000000 : ℝ)=(25006821037609260717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32011252287155443/100000000000000000000 : ℝ)+(6821037609260717/50000000000000000000 : ℝ) ≤ ((1321075792662960847/1321500000000000000 : ℝ)+(447202133729/264300000000000 : ℝ)*((3523/25000 : ℝ)+(11449/100000 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (1321075792662960847/1321500000000000000 : ℝ)+(447202133729/264300000000000 : ℝ)*((3523/25000 : ℝ)+(11449/100000 : ℝ))=(10001111556169803/10000000000000000 : ℝ) by norm_num, show 1+(32011252287155443/100000000000000000000 : ℝ)+(6821037609260717/50000000000000000000 : ℝ)=(100045653327505676877/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32011252287155443/100000000000000000000 : ℝ) ≤ ((1321075792662960847/1321500000000000000 : ℝ)+2*(447202133729/264300000000000 : ℝ)*(3523/25000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (1321075792662960847/1321500000000000000 : ℝ)+2*(447202133729/264300000000000 : ℝ)*(3523/25000 : ℝ)=(2500389689575883/2500000000000000 : ℝ) by norm_num, show 1+2*(32011252287155443/100000000000000000000 : ℝ)=(50032011252287155443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1321075792662960847/1321500000000000000 : ℝ)*(X 1 0+X 2 0)+(447202133729/264300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (1321075792662960847/1321500000000000000 : ℝ)) (alpha := (447202133729/264300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1321075792662960847/1321500000000000000 : ℝ)*(X 0 1+X 2 1)+(447202133729/264300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (1321075792662960847/1321500000000000000 : ℝ)) (alpha := (447202133729/264300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1321075792662960847/1321500000000000000 : ℝ)*(X 0 2+X 1 2)+(447202133729/264300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (11449/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (1321075792662960847/1321500000000000000 : ℝ)) (alpha := (447202133729/264300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131065451/10000000000 : ℝ)*X 0 0+(2695801373/5000000000 : ℝ)*X 0 1+(2633462307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344421017/10000000000 : ℝ)*X 1 0+(-2194285477/10000000000 : ℝ)*X 1 1+(2633462307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344421017/10000000000 : ℝ)*X 2 0+(2633462307/5000000000 : ℝ)*X 2 1+(-2194285477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354077251/10000000000 : ℝ)*X 0 0+(4229982637/10000000000 : ℝ)*X 0 1+(4481729487/10000000000 : ℝ)*X 0 2+(4354077251/10000000000 : ℝ)*X 1 0+(4229982637/10000000000 : ℝ)*X 1 1+(4481729487/10000000000 : ℝ)*X 1 2+(4354077251/10000000000 : ℝ)*X 2 0+(4229982637/10000000000 : ℝ)*X 2 1+(4481729487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065535071/5000000000 : ℝ)*X 0 0+(5267238549/10000000000 : ℝ)*X 0 1+(5391287681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656330417/5000000000 : ℝ)*X 1 0+(-2069922453/10000000000 : ℝ)*X 1 1+(2695643847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062532161/2000000000 : ℝ)*X 2 0+(1347821939/2500000000 : ℝ)*X 2 1+(-2069922407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354086729/10000000000 : ℝ)*X 0 0+(1120273909/2500000000 : ℝ)*X 0 1+(4230618797/10000000000 : ℝ)*X 0 2+(4354086729/10000000000 : ℝ)*X 1 0+(1120273909/2500000000 : ℝ)*X 1 1+(4230618797/10000000000 : ℝ)*X 1 2+(4354086729/10000000000 : ℝ)*X 2 0+(1120273909/2500000000 : ℝ)*X 2 1+(4230618797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60850554324140024578153647/11012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215068537/20000000000000 : ℝ)*(base19) + (1001364153/100000000000000 : ℝ)*(base23) + (9884311/25000000000000 : ℝ)*(lower2) + (69669721/50000000000000 : ℝ)*(upper3) + (84954539/100000000000000 : ℝ)*(upper5) + (2998247082237599/50000000000000 : ℝ)*(major0) + (2998247082237599/50000000000000 : ℝ)*(major1) + (2998247082237599/50000000000000 : ℝ)*(major2) + (250646370531909/3125000000000 : ℝ)*(sp0) + (125323632865517/1562500000000 : ℝ)*(sp1) + (401035628868581/5000000000000 : ℝ)*(sp2) + (993064663771693/25000000000000 : ℝ)*(sp3) + (14860857343/50000000000000 : ℝ)*(sp4) + (15910941527/100000000000000 : ℝ)*(sp7) + (3972274566028299/100000000000000 : ℝ)*(f.failure) + (8020713578735773/100000000000000 : ℝ)*(f.sum) + (72297748324517/13215000000000000000000000000 : ℝ)*base65 + (49845805188791353/66075000000000000000000000000000 : ℝ)*base67 + (2775002187933647/66075000000000000000000000000000 : ℝ)*base70 + (1128526312803183647/66075000000000000000000000000000 : ℝ)*base72 + (2123631508471/6607500000000000000000000000 : ℝ)*base73 + (1730251671905516353/66075000000000000000000000000000 : ℝ)*base75 + (111859551764516353/66075000000000000000000000000000 : ℝ)*base77 + (123604242869441353/66075000000000000000000000000000 : ℝ)*base79 + (45355177147903/13215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (78336197/10000000000000000000000 : ℝ)*base89 + (78336197/10000000000000000000000 : ℝ)*base91 + (78336197/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130873097234767151521232209/22025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845577583/100000000000000 : ℝ)*(base19) + (921000729/100000000000000 : ℝ)*(base23) + (34830831/12500000000000 : ℝ)*(lower1) + (121535433/100000000000000 : ℝ)*(upper3) + (4491299/10000000000000 : ℝ)*(lower4) + (106567507/100000000000000 : ℝ)*(upper5) + (6026835676460251/100000000000000 : ℝ)*(major0) + (6026835676460251/100000000000000 : ℝ)*(major1) + (6026835676460251/100000000000000 : ℝ)*(major2) + (2917885337/50000000000000 : ℝ)*(sp2) + (4030648687671531/50000000000000 : ℝ)*(sp4) + (201532413244137/2500000000000 : ℝ)*(sp5) + (4030645309285829/50000000000000 : ℝ)*(sp6) + (3992373779509917/100000000000000 : ℝ)*(sp7) + (3992373779509917/100000000000000 : ℝ)*(f.failure) + (4030648687671531/50000000000000 : ℝ)*(f.sum) + (218723140211/3303750000000000000000000000 : ℝ)*base65 + (1144330143607187597/132150000000000000000000000000000 : ℝ)*base67 + (928369315762037597/132150000000000000000000000000000 : ℝ)*base69 + (3990830232906737597/132150000000000000000000000000000 : ℝ)*base71 + (612628581001/13215000000000000000000000000 : ℝ)*base74 + (17616194153641337597/132150000000000000000000000000000 : ℝ)*base75 + (2371053169136537597/132150000000000000000000000000000 : ℝ)*base77 + (4809128183298287597/132150000000000000000000000000000 : ℝ)*base79 + (2158426925299/3303750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (54042349/10000000000000000000000 : ℝ)*base90 + (54042349/10000000000000000000000 : ℝ)*base92 + (54042349/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11449/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1218_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1218_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1218_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1218_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
