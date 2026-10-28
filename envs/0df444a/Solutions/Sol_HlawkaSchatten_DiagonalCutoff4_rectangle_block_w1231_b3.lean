-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1231_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:33.556544+00:00
-- url     : https://prove2.me/submissions/5f4d015f-a567-463c-855c-2c6be1613810

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
theorem support_rectangle_w1231_box_0 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-50025107/250000000 : ℝ)*x 0 + (2687503801/5000000000 : ℝ)*x 1 + (1075001447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50025107/250000000 : ℝ)^1053 ≤ (2983635276069/25000000000000 : ℝ)^797 := by
    have hnat : (50025107 : ℕ)^1053*25000000000000^797 ≤ 2983635276069^797*250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50025107 250000000 2983635276069 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687503801/5000000000 : ℝ)^1053 ≤ (44032731429431/100000000000000 : ℝ)^797 := by
    have hnat : (2687503801 : ℕ)^1053*100000000000000^797 ≤ 44032731429431^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687503801 5000000000 44032731429431 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075001447/2000000000 : ℝ)^1053 ≤ (44032727457217/100000000000000 : ℝ)^797 := by
    have hnat : (1075001447 : ℕ)^1053*100000000000000^797 ≤ 44032727457217^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075001447 2000000000 44032727457217 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50025107/250000000 : ℝ), (2687503801/5000000000 : ℝ), (1075001447/2000000000 : ℝ)] ![(2983635276069/25000000000000 : ℝ), (44032731429431/100000000000000 : ℝ), (44032727457217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50025107/250000000 : ℝ)|^1053 ≤ (2983635276069/25000000000000 : ℝ)^797
        have hw : |(-50025107/250000000 : ℝ)|=(50025107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687503801/5000000000 : ℝ)|^1053 ≤ (44032731429431/100000000000000 : ℝ)^797
        have hw : |(2687503801/5000000000 : ℝ)|=(2687503801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075001447/2000000000 : ℝ)|^1053 ≤ (44032727457217/100000000000000 : ℝ)^797
        have hw : |(1075001447/2000000000 : ℝ)|=(1075001447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_1 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165522429/312500000 : ℝ)*x 0 + (-105369391/500000000 : ℝ)*x 1 + (1343751823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165522429/312500000 : ℝ)^1053 ≤ (43187351965473/100000000000000 : ℝ)^797 := by
    have hnat : (165522429 : ℕ)^1053*100000000000000^797 ≤ 43187351965473^797*312500000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165522429 312500000 43187351965473 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105369391/500000000 : ℝ)^1053 ≤ (199686249163/1562500000000 : ℝ)^797 := by
    have hnat : (105369391 : ℕ)^1053*1562500000000^797 ≤ 199686249163^797*500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105369391 500000000 199686249163 1562500000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343751823/2500000000 : ℝ)^1053 ≤ (8806545614831/20000000000000 : ℝ)^797 := by
    have hnat : (1343751823 : ℕ)^1053*20000000000000^797 ≤ 8806545614831^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343751823 2500000000 8806545614831 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165522429/312500000 : ℝ), (-105369391/500000000 : ℝ), (1343751823/2500000000 : ℝ)] ![(43187351965473/100000000000000 : ℝ), (199686249163/1562500000000 : ℝ), (8806545614831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165522429/312500000 : ℝ)|^1053 ≤ (43187351965473/100000000000000 : ℝ)^797
        have hw : |(165522429/312500000 : ℝ)|=(165522429/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105369391/500000000 : ℝ)|^1053 ≤ (199686249163/1562500000000 : ℝ)^797
        have hw : |(-105369391/500000000 : ℝ)|=(105369391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343751823/2500000000 : ℝ)|^1053 ≤ (8806545614831/20000000000000 : ℝ)^797
        have hw : |(1343751823/2500000000 : ℝ)|=(1343751823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_2 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5296717787/10000000000 : ℝ)*x 0 + (1075001479/2000000000 : ℝ)*x 1 + (-2107387601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296717787/10000000000 : ℝ)^1053 ≤ (1349604768783/3125000000000 : ℝ)^797 := by
    have hnat : (5296717787 : ℕ)^1053*3125000000000^797 ≤ 1349604768783^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296717787 10000000000 1349604768783 3125000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075001479/2000000000 : ℝ)^1053 ≤ (11008182297243/25000000000000 : ℝ)^797 := by
    have hnat : (1075001479 : ℕ)^1053*25000000000000^797 ≤ 11008182297243^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075001479 2000000000 11008182297243 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107387601/10000000000 : ℝ)^1053 ≤ (1597489773969/12500000000000 : ℝ)^797 := by
    have hnat : (2107387601 : ℕ)^1053*12500000000000^797 ≤ 1597489773969^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107387601 10000000000 1597489773969 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296717787/10000000000 : ℝ), (1075001479/2000000000 : ℝ), (-2107387601/10000000000 : ℝ)] ![(1349604768783/3125000000000 : ℝ), (11008182297243/25000000000000 : ℝ), (1597489773969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296717787/10000000000 : ℝ)|^1053 ≤ (1349604768783/3125000000000 : ℝ)^797
        have hw : |(5296717787/10000000000 : ℝ)|=(5296717787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075001479/2000000000 : ℝ)|^1053 ≤ (11008182297243/25000000000000 : ℝ)^797
        have hw : |(1075001479/2000000000 : ℝ)|=(1075001479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107387601/10000000000 : ℝ)|^1053 ≤ (1597489773969/12500000000000 : ℝ)^797
        have hw : |(-2107387601/10000000000 : ℝ)|=(2107387601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_3 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (139341241/312500000 : ℝ)*x 0 + (4301018397/10000000000 : ℝ)*x 1 + (2150508813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139341241/312500000 : ℝ)^1053 ≤ (6880034690941/20000000000000 : ℝ)^797 := by
    have hnat : (139341241 : ℕ)^1053*20000000000000^797 ≤ 6880034690941^797*312500000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139341241 312500000 6880034690941 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4301018397/10000000000 : ℝ)^1053 ≤ (16399958573399/50000000000000 : ℝ)^797 := by
    have hnat : (4301018397 : ℕ)^1053*50000000000000^797 ≤ 16399958573399^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301018397 10000000000 16399958573399 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150508813/5000000000 : ℝ)^1053 ≤ (65599818757/200000000000 : ℝ)^797 := by
    have hnat : (2150508813 : ℕ)^1053*200000000000^797 ≤ 65599818757^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150508813 5000000000 65599818757 200000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(139341241/312500000 : ℝ), (4301018397/10000000000 : ℝ), (2150508813/5000000000 : ℝ)] ![(6880034690941/20000000000000 : ℝ), (16399958573399/50000000000000 : ℝ), (65599818757/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(139341241/312500000 : ℝ)|^1053 ≤ (6880034690941/20000000000000 : ℝ)^797
        have hw : |(139341241/312500000 : ℝ)|=(139341241/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4301018397/10000000000 : ℝ)|^1053 ≤ (16399958573399/50000000000000 : ℝ)^797
        have hw : |(4301018397/10000000000 : ℝ)|=(4301018397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150508813/5000000000 : ℝ)|^1053 ≤ (65599818757/200000000000 : ℝ)^797
        have hw : |(2150508813/5000000000 : ℝ)|=(2150508813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_4 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-56261421/250000000 : ℝ)*x 0 + (1056434513/2000000000 : ℝ)*x 1 + (1056434539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56261421/250000000 : ℝ)^1053 ≤ (6969267142187/50000000000000 : ℝ)^797 := by
    have hnat : (56261421 : ℕ)^1053*50000000000000^797 ≤ 6969267142187^797*250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56261421 250000000 6969267142187 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056434513/2000000000 : ℝ)^1053 ≤ (21515366077707/50000000000000 : ℝ)^797 := by
    have hnat : (1056434513 : ℕ)^1053*50000000000000^797 ≤ 21515366077707^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056434513 2000000000 21515366077707 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056434539/2000000000 : ℝ)^1053 ≤ (43030733554613/100000000000000 : ℝ)^797 := by
    have hnat : (1056434539 : ℕ)^1053*100000000000000^797 ≤ 43030733554613^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056434539 2000000000 43030733554613 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56261421/250000000 : ℝ), (1056434513/2000000000 : ℝ), (1056434539/2000000000 : ℝ)] ![(6969267142187/50000000000000 : ℝ), (21515366077707/50000000000000 : ℝ), (43030733554613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56261421/250000000 : ℝ)|^1053 ≤ (6969267142187/50000000000000 : ℝ)^797
        have hw : |(-56261421/250000000 : ℝ)|=(56261421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056434513/2000000000 : ℝ)|^1053 ≤ (21515366077707/50000000000000 : ℝ)^797
        have hw : |(1056434513/2000000000 : ℝ)|=(1056434513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056434539/2000000000 : ℝ)|^1053 ≤ (43030733554613/100000000000000 : ℝ)^797
        have hw : |(1056434539/2000000000 : ℝ)|=(1056434539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_5 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5362175549/10000000000 : ℝ)*x 0 + (-214416001/1000000000 : ℝ)*x 1 + (5282172627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362175549/10000000000 : ℝ)^1053 ≤ (21946948672407/50000000000000 : ℝ)^797 := by
    have hnat : (5362175549 : ℕ)^1053*50000000000000^797 ≤ 21946948672407^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362175549 10000000000 21946948672407 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214416001/1000000000 : ℝ)^1053 ≤ (13075369821779/100000000000000 : ℝ)^797 := by
    have hnat : (214416001 : ℕ)^1053*100000000000000^797 ≤ 13075369821779^797*1000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214416001 1000000000 13075369821779 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282172627/10000000000 : ℝ)^1053 ≤ (1721229312909/4000000000000 : ℝ)^797 := by
    have hnat : (5282172627 : ℕ)^1053*4000000000000^797 ≤ 1721229312909^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282172627 10000000000 1721229312909 4000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362175549/10000000000 : ℝ), (-214416001/1000000000 : ℝ), (5282172627/10000000000 : ℝ)] ![(21946948672407/50000000000000 : ℝ), (13075369821779/100000000000000 : ℝ), (1721229312909/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362175549/10000000000 : ℝ)|^1053 ≤ (21946948672407/50000000000000 : ℝ)^797
        have hw : |(5362175549/10000000000 : ℝ)|=(5362175549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214416001/1000000000 : ℝ)|^1053 ≤ (13075369821779/100000000000000 : ℝ)^797
        have hw : |(-214416001/1000000000 : ℝ)|=(214416001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282172627/10000000000 : ℝ)|^1053 ≤ (1721229312909/4000000000000 : ℝ)^797
        have hw : |(5282172627/10000000000 : ℝ)|=(5282172627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_6 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (335135967/625000000 : ℝ)*x 0 + (132054317/250000000 : ℝ)*x 1 + (-1072080021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335135967/625000000 : ℝ)^1053 ≤ (21946948256023/50000000000000 : ℝ)^797 := by
    have hnat : (335135967 : ℕ)^1053*50000000000000^797 ≤ 21946948256023^797*625000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335135967 625000000 21946948256023 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132054317/250000000 : ℝ)^1053 ≤ (43030733393167/100000000000000 : ℝ)^797 := by
    have hnat : (132054317 : ℕ)^1053*100000000000000^797 ≤ 43030733393167^797*250000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132054317 250000000 43030733393167 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072080021/5000000000 : ℝ)^1053 ≤ (13075370079599/100000000000000 : ℝ)^797 := by
    have hnat : (1072080021 : ℕ)^1053*100000000000000^797 ≤ 13075370079599^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072080021 5000000000 13075370079599 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335135967/625000000 : ℝ), (132054317/250000000 : ℝ), (-1072080021/5000000000 : ℝ)] ![(21946948256023/50000000000000 : ℝ), (43030733393167/100000000000000 : ℝ), (13075370079599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335135967/625000000 : ℝ)|^1053 ≤ (21946948256023/50000000000000 : ℝ)^797
        have hw : |(335135967/625000000 : ℝ)|=(335135967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132054317/250000000 : ℝ)|^1053 ≤ (43030733393167/100000000000000 : ℝ)^797
        have hw : |(132054317/250000000 : ℝ)|=(132054317/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072080021/5000000000 : ℝ)|^1053 ≤ (13075370079599/100000000000000 : ℝ)^797
        have hw : |(-1072080021/5000000000 : ℝ)|=(1072080021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_7 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4245254359/10000000000 : ℝ)*x 0 + (4407830443/10000000000 : ℝ)*x 1 + (4407830579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245254359/10000000000 : ℝ)^1053 ≤ (16119616819517/50000000000000 : ℝ)^797 := by
    have hnat : (4245254359 : ℕ)^1053*50000000000000^797 ≤ 16119616819517^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245254359 10000000000 16119616819517 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407830443/10000000000 : ℝ)^1053 ≤ (16940191241207/50000000000000 : ℝ)^797 := by
    have hnat : (4407830443 : ℕ)^1053*50000000000000^797 ≤ 16940191241207^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407830443 10000000000 16940191241207 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4407830579/10000000000 : ℝ)^1053 ≤ (33880383863537/100000000000000 : ℝ)^797 := by
    have hnat : (4407830579 : ℕ)^1053*100000000000000^797 ≤ 33880383863537^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407830579 10000000000 33880383863537 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245254359/10000000000 : ℝ), (4407830443/10000000000 : ℝ), (4407830579/10000000000 : ℝ)] ![(16119616819517/50000000000000 : ℝ), (16940191241207/50000000000000 : ℝ), (33880383863537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245254359/10000000000 : ℝ)|^1053 ≤ (16119616819517/50000000000000 : ℝ)^797
        have hw : |(4245254359/10000000000 : ℝ)|=(4245254359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407830443/10000000000 : ℝ)|^1053 ≤ (16940191241207/50000000000000 : ℝ)^797
        have hw : |(4407830443/10000000000 : ℝ)|=(4407830443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4407830579/10000000000 : ℝ)|^1053 ≤ (33880383863537/100000000000000 : ℝ)^797
        have hw : |(4407830579/10000000000 : ℝ)|=(4407830579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_8 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099097929/5000000000 : ℝ)*x 0 + (1304717421/2500000000 : ℝ)*x 1 + (2692310149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099097929/5000000000 : ℝ)^1053 ≤ (675624112207/5000000000000 : ℝ)^797 := by
    have hnat : (1099097929 : ℕ)^1053*5000000000000^797 ≤ 675624112207^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099097929 5000000000 675624112207 5000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304717421/2500000000 : ℝ)^1053 ≤ (21175356847693/50000000000000 : ℝ)^797 := by
    have hnat : (1304717421 : ℕ)^1053*50000000000000^797 ≤ 21175356847693^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304717421 2500000000 21175356847693 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692310149/5000000000 : ℝ)^1053 ≤ (8827360809121/20000000000000 : ℝ)^797 := by
    have hnat : (2692310149 : ℕ)^1053*20000000000000^797 ≤ 8827360809121^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692310149 5000000000 8827360809121 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099097929/5000000000 : ℝ), (1304717421/2500000000 : ℝ), (2692310149/5000000000 : ℝ)] ![(675624112207/5000000000000 : ℝ), (21175356847693/50000000000000 : ℝ), (8827360809121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099097929/5000000000 : ℝ)|^1053 ≤ (675624112207/5000000000000 : ℝ)^797
        have hw : |(-1099097929/5000000000 : ℝ)|=(1099097929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304717421/2500000000 : ℝ)|^1053 ≤ (21175356847693/50000000000000 : ℝ)^797
        have hw : |(1304717421/2500000000 : ℝ)|=(1304717421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692310149/5000000000 : ℝ)|^1053 ≤ (8827360809121/20000000000000 : ℝ)^797
        have hw : |(2692310149/5000000000 : ℝ)|=(2692310149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_9 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322484191/2500000000 : ℝ)*x 0 + (-420702473/2000000000 : ℝ)*x 1 + (5384620241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322484191/2500000000 : ℝ)^1053 ≤ (10778579625081/25000000000000 : ℝ)^797 := by
    have hnat : (1322484191 : ℕ)^1053*25000000000000^797 ≤ 10778579625081^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322484191 2500000000 10778579625081 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420702473/2000000000 : ℝ)^1053 ≤ (796804878879/6250000000000 : ℝ)^797 := by
    have hnat : (420702473 : ℕ)^1053*6250000000000^797 ≤ 796804878879^797*2000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420702473 2000000000 796804878879 6250000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384620241/10000000000 : ℝ)^1053 ≤ (44136803428313/100000000000000 : ℝ)^797 := by
    have hnat : (5384620241 : ℕ)^1053*100000000000000^797 ≤ 44136803428313^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384620241 10000000000 44136803428313 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322484191/2500000000 : ℝ), (-420702473/2000000000 : ℝ), (5384620241/10000000000 : ℝ)] ![(10778579625081/25000000000000 : ℝ), (796804878879/6250000000000 : ℝ), (44136803428313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322484191/2500000000 : ℝ)|^1053 ≤ (10778579625081/25000000000000 : ℝ)^797
        have hw : |(1322484191/2500000000 : ℝ)|=(1322484191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420702473/2000000000 : ℝ)|^1053 ≤ (796804878879/6250000000000 : ℝ)^797
        have hw : |(-420702473/2000000000 : ℝ)|=(420702473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384620241/10000000000 : ℝ)|^1053 ≤ (44136803428313/100000000000000 : ℝ)^797
        have hw : |(5384620241/10000000000 : ℝ)|=(5384620241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_10 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322484189/2500000000 : ℝ)*x 0 + (2692310163/5000000000 : ℝ)*x 1 + (-105175613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322484189/2500000000 : ℝ)^1053 ≤ (43114318414179/100000000000000 : ℝ)^797 := by
    have hnat : (1322484189 : ℕ)^1053*100000000000000^797 ≤ 43114318414179^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322484189 2500000000 43114318414179 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692310163/5000000000 : ℝ)^1053 ≤ (11034201087209/25000000000000 : ℝ)^797 := by
    have hnat : (2692310163 : ℕ)^1053*25000000000000^797 ≤ 11034201087209^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692310163 5000000000 11034201087209 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105175613/500000000 : ℝ)^1053 ≤ (3187219305319/25000000000000 : ℝ)^797 := by
    have hnat : (105175613 : ℕ)^1053*25000000000000^797 ≤ 3187219305319^797*500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105175613 500000000 3187219305319 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322484189/2500000000 : ℝ), (2692310163/5000000000 : ℝ), (-105175613/500000000 : ℝ)] ![(43114318414179/100000000000000 : ℝ), (11034201087209/25000000000000 : ℝ), (3187219305319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322484189/2500000000 : ℝ)|^1053 ≤ (43114318414179/100000000000000 : ℝ)^797
        have hw : |(1322484189/2500000000 : ℝ)|=(1322484189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692310163/5000000000 : ℝ)|^1053 ≤ (11034201087209/25000000000000 : ℝ)^797
        have hw : |(2692310163/5000000000 : ℝ)|=(2692310163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105175613/500000000 : ℝ)|^1053 ≤ (3187219305319/25000000000000 : ℝ)^797
        have hw : |(-105175613/500000000 : ℝ)|=(105175613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_11 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4480771631/10000000000 : ℝ)*x 0 + (2144975743/5000000000 : ℝ)*x 1 + (85799031/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4480771631/10000000000 : ℝ)^1053 ≤ (34623084669231/100000000000000 : ℝ)^797 := by
    have hnat : (4480771631 : ℕ)^1053*100000000000000^797 ≤ 34623084669231^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480771631 10000000000 34623084669231 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144975743/5000000000 : ℝ)^1053 ≤ (6537691467163/20000000000000 : ℝ)^797 := by
    have hnat : (2144975743 : ℕ)^1053*20000000000000^797 ≤ 6537691467163^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144975743 5000000000 6537691467163 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85799031/200000000 : ℝ)^1053 ≤ (32688457980121/100000000000000 : ℝ)^797 := by
    have hnat : (85799031 : ℕ)^1053*100000000000000^797 ≤ 32688457980121^797*200000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85799031 200000000 32688457980121 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4480771631/10000000000 : ℝ), (2144975743/5000000000 : ℝ), (85799031/200000000 : ℝ)] ![(34623084669231/100000000000000 : ℝ), (6537691467163/20000000000000 : ℝ), (32688457980121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4480771631/10000000000 : ℝ)|^1053 ≤ (34623084669231/100000000000000 : ℝ)^797
        have hw : |(4480771631/10000000000 : ℝ)|=(4480771631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2144975743/5000000000 : ℝ)|^1053 ≤ (6537691467163/20000000000000 : ℝ)^797
        have hw : |(2144975743/5000000000 : ℝ)|=(2144975743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85799031/200000000 : ℝ)|^1053 ≤ (32688457980121/100000000000000 : ℝ)^797
        have hw : |(85799031/200000000 : ℝ)|=(85799031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_12 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026765609/5000000000 : ℝ)*x 0 + (5437094779/10000000000 : ℝ)*x 1 + (329631069/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026765609/5000000000 : ℝ)^1053 ≤ (6175094795717/50000000000000 : ℝ)^797 := by
    have hnat : (1026765609 : ℕ)^1053*50000000000000^797 ≤ 6175094795717^797*5000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026765609 5000000000 6175094795717 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437094779/10000000000 : ℝ)^1053 ≤ (11176493411763/25000000000000 : ℝ)^797 := by
    have hnat : (5437094779 : ℕ)^1053*25000000000000^797 ≤ 11176493411763^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437094779 10000000000 11176493411763 25000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329631069/625000000 : ℝ)^1053 ≤ (5367979593059/12500000000000 : ℝ)^797 := by
    have hnat : (329631069 : ℕ)^1053*12500000000000^797 ≤ 5367979593059^797*625000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329631069 625000000 5367979593059 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026765609/5000000000 : ℝ), (5437094779/10000000000 : ℝ), (329631069/625000000 : ℝ)] ![(6175094795717/50000000000000 : ℝ), (11176493411763/25000000000000 : ℝ), (5367979593059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026765609/5000000000 : ℝ)|^1053 ≤ (6175094795717/50000000000000 : ℝ)^797
        have hw : |(-1026765609/5000000000 : ℝ)|=(1026765609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437094779/10000000000 : ℝ)|^1053 ≤ (11176493411763/25000000000000 : ℝ)^797
        have hw : |(5437094779/10000000000 : ℝ)|=(5437094779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329631069/625000000 : ℝ)|^1053 ≤ (5367979593059/12500000000000 : ℝ)^797
        have hw : |(329631069/625000000 : ℝ)|=(329631069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_13 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5367866999/10000000000 : ℝ)*x 0 + (-2147302653/10000000000 : ℝ)*x 1 + (5274097639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367866999/10000000000 : ℝ)^1053 ≤ (21977730904069/50000000000000 : ℝ)^797 := by
    have hnat : (5367866999 : ℕ)^1053*50000000000000^797 ≤ 21977730904069^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367866999 10000000000 21977730904069 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147302653/10000000000 : ℝ)^1053 ≤ (1637586959267/12500000000000 : ℝ)^797 := by
    have hnat : (2147302653 : ℕ)^1053*12500000000000^797 ≤ 1637586959267^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147302653 10000000000 1637586959267 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274097639/10000000000 : ℝ)^1053 ≤ (8588768499977/20000000000000 : ℝ)^797 := by
    have hnat : (5274097639 : ℕ)^1053*20000000000000^797 ≤ 8588768499977^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274097639 10000000000 8588768499977 20000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367866999/10000000000 : ℝ), (-2147302653/10000000000 : ℝ), (5274097639/10000000000 : ℝ)] ![(21977730904069/50000000000000 : ℝ), (1637586959267/12500000000000 : ℝ), (8588768499977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367866999/10000000000 : ℝ)|^1053 ≤ (21977730904069/50000000000000 : ℝ)^797
        have hw : |(5367866999/10000000000 : ℝ)|=(5367866999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147302653/10000000000 : ℝ)|^1053 ≤ (1637586959267/12500000000000 : ℝ)^797
        have hw : |(-2147302653/10000000000 : ℝ)|=(2147302653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274097639/10000000000 : ℝ)|^1053 ≤ (8588768499977/20000000000000 : ℝ)^797
        have hw : |(5274097639/10000000000 : ℝ)|=(5274097639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_14 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5367867419/10000000000 : ℝ)*x 0 + (527409729/1000000000 : ℝ)*x 1 + (-536825639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367867419/10000000000 : ℝ)^1053 ≤ (5494433294007/12500000000000 : ℝ)^797 := by
    have hnat : (5367867419 : ℕ)^1053*12500000000000^797 ≤ 5494433294007^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367867419 10000000000 5494433294007 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527409729/1000000000 : ℝ)^1053 ≤ (42943838745419/100000000000000 : ℝ)^797 := by
    have hnat : (527409729 : ℕ)^1053*100000000000000^797 ≤ 42943838745419^797*1000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527409729 1000000000 42943838745419 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536825639/2500000000 : ℝ)^1053 ≤ (13100694892251/100000000000000 : ℝ)^797 := by
    have hnat : (536825639 : ℕ)^1053*100000000000000^797 ≤ 13100694892251^797*2500000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536825639 2500000000 13100694892251 100000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367867419/10000000000 : ℝ), (527409729/1000000000 : ℝ), (-536825639/2500000000 : ℝ)] ![(5494433294007/12500000000000 : ℝ), (42943838745419/100000000000000 : ℝ), (13100694892251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367867419/10000000000 : ℝ)|^1053 ≤ (5494433294007/12500000000000 : ℝ)^797
        have hw : |(5367867419/10000000000 : ℝ)|=(5367867419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527409729/1000000000 : ℝ)|^1053 ≤ (42943838745419/100000000000000 : ℝ)^797
        have hw : |(527409729/1000000000 : ℝ)|=(527409729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536825639/2500000000 : ℝ)|^1053 ≤ (13100694892251/100000000000000 : ℝ)^797
        have hw : |(-536825639/2500000000 : ℝ)|=(536825639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1231_box_15 (p : ℝ) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ)) (x : Fin 3 → ℝ) :
    (422643697/1000000000 : ℝ)*x 0 + (4417116523/10000000000 : ℝ)*x 1 + (4417116577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422643697/1000000000 : ℝ)^1053 ≤ (3205056452119/10000000000000 : ℝ)^797 := by
    have hnat : (422643697 : ℕ)^1053*10000000000000^797 ≤ 3205056452119^797*1000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422643697 1000000000 3205056452119 10000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417116523/10000000000 : ℝ)^1053 ≤ (4246839682251/12500000000000 : ℝ)^797 := by
    have hnat : (4417116523 : ℕ)^1053*12500000000000^797 ≤ 4246839682251^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417116523 10000000000 4246839682251 12500000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417116577/10000000000 : ℝ)^1053 ≤ (16987359003383/50000000000000 : ℝ)^797 := by
    have hnat : (4417116577 : ℕ)^1053*50000000000000^797 ≤ 16987359003383^797*10000000000^1053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417116577 10000000000 16987359003383 50000000000000 1053 797 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1053/256 : ℝ)) 1053 797 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422643697/1000000000 : ℝ), (4417116523/10000000000 : ℝ), (4417116577/10000000000 : ℝ)] ![(3205056452119/10000000000000 : ℝ), (4246839682251/12500000000000 : ℝ), (16987359003383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422643697/1000000000 : ℝ)|^1053 ≤ (3205056452119/10000000000000 : ℝ)^797
        have hw : |(422643697/1000000000 : ℝ)|=(422643697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417116523/10000000000 : ℝ)|^1053 ≤ (4246839682251/12500000000000 : ℝ)^797
        have hw : |(4417116523/10000000000 : ℝ)|=(4417116523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417116577/10000000000 : ℝ)|^1053 ≤ (16987359003383/50000000000000 : ℝ)^797
        have hw : |(4417116577/10000000000 : ℝ)|=(4417116577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1231_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12449/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59369/100000 : ℝ) ∧ (20019/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41661/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5733/50000 : ℝ) ^ (8423/2048 : ℝ) ≤ (2707609476713811/20000000000000000000 : ℝ) := by
    have hpowers : (5733/50000 : ℝ)^8423 ≤ (2707609476713811/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5733 : ℕ)^8423*20000000000000000000^2048 ≤ 2707609476713811^2048*50000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5733 50000 2707609476713811 20000000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5733/50000 : ℝ)) (X := (2707609476713811/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (8423/2048 : ℝ) ≤ (3167094150255411/10000000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^8423 ≤ (3167094150255411/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7049 : ℕ)^8423*10000000000000000000^2048 ≤ 3167094150255411^2048*50000^8423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 3167094150255411 10000000000000000000 8423 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (3167094150255411/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002707609476713811/10000000000000000000 : ℝ) ≤ (10000658270938989/10000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (10002707609476713811/10000000000000000000 : ℝ)^2048 ≤ (10000658270938989/10000000000000000 : ℝ)^8423 := by
      have hnat : (10002707609476713811 : ℕ)^2048*10000000000000000^8423 ≤ 10000658270938989^8423*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002707609476713811 10000000000000000000 10000658270938989 10000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000658270938989/10000000000000000 : ℝ)) (X := (10002707609476713811/10000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009041797777224633/20000000000000000000 : ℝ) ≤ (2500274760100761/2500000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (20009041797777224633/20000000000000000000 : ℝ)^2048 ≤ (2500274760100761/2500000000000000 : ℝ)^8423 := by
      have hnat : (20009041797777224633 : ℕ)^2048*2500000000000000^8423 ≤ 2500274760100761^8423*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009041797777224633 20000000000000000000 2500274760100761 2500000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500274760100761/2500000000000000 : ℝ)) (X := (20009041797777224633/20000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003167094150255411/5000000000000000000 : ℝ) ≤ (10001539809867099/10000000000000000 : ℝ) ^ (8423/2048 : ℝ) := by
    have hpowers : (5003167094150255411/5000000000000000000 : ℝ)^2048 ≤ (10001539809867099/10000000000000000 : ℝ)^8423 := by
      have hnat : (5003167094150255411 : ℕ)^2048*10000000000000000^8423 ≤ 10001539809867099^8423*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003167094150255411 5000000000000000000 10001539809867099 10000000000000000 2048 8423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001539809867099/10000000000000000 : ℝ)) (X := (5003167094150255411/5000000000000000000 : ℝ)) (by norm_num) 8423 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2707609476713811/20000000000000000000 : ℝ) ≤ ((939700887277203921/940000000000000000 : ℝ)+2*(88153892811/52640000000000 : ℝ)*(5733/50000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (939700887277203921/940000000000000000 : ℝ)+2*(88153892811/52640000000000 : ℝ)*(5733/50000 : ℝ)=(10000658270938989/10000000000000000 : ℝ) by norm_num, show 1+2*(2707609476713811/20000000000000000000 : ℝ)=(10002707609476713811/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3167094150255411/10000000000000000000 : ℝ)+(2707609476713811/20000000000000000000 : ℝ) ≤ ((939700887277203921/940000000000000000 : ℝ)+(88153892811/52640000000000 : ℝ)*((7049/50000 : ℝ)+(5733/50000 : ℝ)))^(8423/2048 : ℝ) := by
    rw [show (939700887277203921/940000000000000000 : ℝ)+(88153892811/52640000000000 : ℝ)*((7049/50000 : ℝ)+(5733/50000 : ℝ))=(2500274760100761/2500000000000000 : ℝ) by norm_num, show 1+(3167094150255411/10000000000000000000 : ℝ)+(2707609476713811/20000000000000000000 : ℝ)=(20009041797777224633/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3167094150255411/10000000000000000000 : ℝ) ≤ ((939700887277203921/940000000000000000 : ℝ)+2*(88153892811/52640000000000 : ℝ)*(7049/50000 : ℝ))^(8423/2048 : ℝ) := by
    rw [show (939700887277203921/940000000000000000 : ℝ)+2*(88153892811/52640000000000 : ℝ)*(7049/50000 : ℝ)=(10001539809867099/10000000000000000 : ℝ) by norm_num, show 1+2*(3167094150255411/10000000000000000000 : ℝ)=(5003167094150255411/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (939700887277203921/940000000000000000 : ℝ)*(X 1 0+X 2 0)+(88153892811/52640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (939700887277203921/940000000000000000 : ℝ)) (alpha := (88153892811/52640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (939700887277203921/940000000000000000 : ℝ)*(X 0 1+X 2 1)+(88153892811/52640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (939700887277203921/940000000000000000 : ℝ)) (alpha := (88153892811/52640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (939700887277203921/940000000000000000 : ℝ)*(X 0 2+X 1 2)+(88153892811/52640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8423/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (939700887277203921/940000000000000000 : ℝ)) (alpha := (88153892811/52640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50025107/250000000 : ℝ)*X 0 0+(2687503801/5000000000 : ℝ)*X 0 1+(1075001447/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165522429/312500000 : ℝ)*X 1 0+(-105369391/500000000 : ℝ)*X 1 1+(1343751823/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296717787/10000000000 : ℝ)*X 2 0+(1075001479/2000000000 : ℝ)*X 2 1+(-2107387601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((139341241/312500000 : ℝ)*X 0 0+(4301018397/10000000000 : ℝ)*X 0 1+(2150508813/5000000000 : ℝ)*X 0 2+(139341241/312500000 : ℝ)*X 1 0+(4301018397/10000000000 : ℝ)*X 1 1+(2150508813/5000000000 : ℝ)*X 1 2+(139341241/312500000 : ℝ)*X 2 0+(4301018397/10000000000 : ℝ)*X 2 1+(2150508813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-56261421/250000000 : ℝ)*X 0 0+(1056434513/2000000000 : ℝ)*X 0 1+(1056434539/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362175549/10000000000 : ℝ)*X 1 0+(-214416001/1000000000 : ℝ)*X 1 1+(5282172627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335135967/625000000 : ℝ)*X 2 0+(132054317/250000000 : ℝ)*X 2 1+(-1072080021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4245254359/10000000000 : ℝ)*X 0 0+(4407830443/10000000000 : ℝ)*X 0 1+(4407830579/10000000000 : ℝ)*X 0 2+(4245254359/10000000000 : ℝ)*X 1 0+(4407830443/10000000000 : ℝ)*X 1 1+(4407830579/10000000000 : ℝ)*X 1 2+(4245254359/10000000000 : ℝ)*X 2 0+(4407830443/10000000000 : ℝ)*X 2 1+(4407830579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1099097929/5000000000 : ℝ)*X 0 0+(1304717421/2500000000 : ℝ)*X 0 1+(2692310149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322484191/2500000000 : ℝ)*X 1 0+(-420702473/2000000000 : ℝ)*X 1 1+(5384620241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322484189/2500000000 : ℝ)*X 2 0+(2692310163/5000000000 : ℝ)*X 2 1+(-105175613/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4480771631/10000000000 : ℝ)*X 0 0+(2144975743/5000000000 : ℝ)*X 0 1+(85799031/200000000 : ℝ)*X 0 2+(4480771631/10000000000 : ℝ)*X 1 0+(2144975743/5000000000 : ℝ)*X 1 1+(85799031/200000000 : ℝ)*X 1 2+(4480771631/10000000000 : ℝ)*X 2 0+(2144975743/5000000000 : ℝ)*X 2 1+(85799031/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1026765609/5000000000 : ℝ)*X 0 0+(5437094779/10000000000 : ℝ)*X 0 1+(329631069/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367866999/10000000000 : ℝ)*X 1 0+(-2147302653/10000000000 : ℝ)*X 1 1+(5274097639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367867419/10000000000 : ℝ)*X 2 0+(527409729/1000000000 : ℝ)*X 2 1+(-536825639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((422643697/1000000000 : ℝ)*X 0 0+(4417116523/10000000000 : ℝ)*X 0 1+(4417116577/10000000000 : ℝ)*X 0 2+(422643697/1000000000 : ℝ)*X 1 0+(4417116523/10000000000 : ℝ)*X 1 1+(4417116577/10000000000 : ℝ)*X 1 2+(422643697/1000000000 : ℝ)*X 2 0+(4417116523/10000000000 : ℝ)*X 2 1+(4417116577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1231_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12449/20000 : ℝ) ≤ (-1599815689821482843057593203249/2570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (40673931/100000000000000 : ℝ)*(upper0) + (99820003/100000000000000 : ℝ)*(upper1) + (43322207/50000000000000 : ℝ)*(upper2) + (15829923/25000000000000 : ℝ)*(upper3) + (8333369/5000000000000 : ℝ)*(upper5) + (124818377811397/3125000000000 : ℝ)*(major0) + (124818377811397/3125000000000 : ℝ)*(major1) + (124818377811397/3125000000000 : ℝ)*(major2) + (1730628261/25000000000000 : ℝ)*(sp2) + (10352974877/100000000000000 : ℝ)*(sp3) + (5367694282044567/100000000000000 : ℝ)*(sp4) + (5367694282044567/100000000000000 : ℝ)*(sp5) + (5367687359531523/100000000000000 : ℝ)*(sp6) + (660354725343413/25000000000000 : ℝ)*(sp7) + (2641429254348529/100000000000000 : ℝ)*(f.failure) + (5367694282044567/100000000000000 : ℝ)*(f.sum) + (6291511147/8225000000000000000000000 : ℝ)*base66 + (291798507753411541/20562500000000000000000000000000 : ℝ)*base68 + (2130574988424349041/20562500000000000000000000000000 : ℝ)*base70 + (48007706786849041/20562500000000000000000000000000 : ℝ)*base72 + (829598671653/329000000000000000000000000 : ℝ)*base73 + (50081172616599041/20562500000000000000000000000000 : ℝ)*base76 + (89955724982411541/20562500000000000000000000000000 : ℝ)*base78 + (2217676799635025959/20562500000000000000000000000000 : ℝ)*base79 + (3201359218751/10281250000000000000000000 : ℝ)*base82 + (70122531/10000000000000000000000 : ℝ)*base89 + (70122531/10000000000000000000000 : ℝ)*base91 + (70122531/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59369/100000 : ℝ) ≤ (13952185569700400908959993216027/23500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93719009/50000000000000 : ℝ)*(upper3) + (54970559/25000000000000 : ℝ)*(upper4) + (3855563/50000000000000 : ℝ)*(lower5) + (2029899230552557/50000000000000 : ℝ)*(major0) + (2029899230552557/50000000000000 : ℝ)*(major1) + (2029899230552557/50000000000000 : ℝ)*(major2) + (5414975074345127/100000000000000 : ℝ)*(sp0) + (108296243948901/2000000000000 : ℝ)*(sp1) + (1353744375731797/25000000000000 : ℝ)*(sp2) + (335601924110373/12500000000000 : ℝ)*(sp3) + (10498639607/100000000000000 : ℝ)*(sp6) + (1596809511/50000000000000 : ℝ)*(sp7) + (3231805417/25000000000000 : ℝ)*(sp8) + (10987757609/6250000000000 : ℝ)*(sp9) + (1342409293251003/50000000000000 : ℝ)*(f.failure) + (1082997600313359/20000000000000 : ℝ)*(f.sum) + (40781859437/37600000000000000000000000 : ℝ)*base65 + (354341286072100997/47000000000000000000000000000000 : ℝ)*base67 + (285953989135100997/47000000000000000000000000000000 : ℝ)*base69 + (218279643658100997/47000000000000000000000000000000 : ℝ)*base71 + (1523502911169/188000000000000000000000000 : ℝ)*base73 + (722127431370100997/47000000000000000000000000000000 : ℝ)*base75 + (109692270390100997/47000000000000000000000000000000 : ℝ)*base77 + (136349474334100997/47000000000000000000000000000000 : ℝ)*base79 + (73196581159/188000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (21471583/5000000000000000000000 : ℝ)*base90 + (21471583/5000000000000000000000 : ℝ)*base92 + (21471583/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20019/25000 : ℝ) ≤ (131729632171775861606960041357107/164500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73869769/100000000000000 : ℝ)*(lower3) + (200399/781250000000 : ℝ)*(upper4) + (8782889/100000000000000 : ℝ)*(lower5) + (4526735507289573/100000000000000 : ℝ)*(major0) + (4526735507289573/100000000000000 : ℝ)*(major1) + (4526735507289573/100000000000000 : ℝ)*(major2) + (387033523/20000000000000 : ℝ)*(sp0) + (10751386881/25000000000000 : ℝ)*(sp1) + (87950506973/100000000000000 : ℝ)*(sp2) + (9777222969/25000000000000 : ℝ)*(sp3) + (754145449276021/12500000000000 : ℝ)*(sp8) + (6033122523828259/100000000000000 : ℝ)*(sp9) + (6033077578868811/100000000000000 : ℝ)*(sp10) + (1496786720863767/50000000000000 : ℝ)*(sp11) + (299361255061941/10000000000000 : ℝ)*(f.failure) + (6033165529375783/100000000000000 : ℝ)*(f.sum) + (849073871801/2632000000000000000000000000 : ℝ)*base66 + (2817603251784985131/658000000000000000000000000000000 : ℝ)*base67 + (9473519194418985131/658000000000000000000000000000000 : ℝ)*base69 + (409243912776985131/658000000000000000000000000000000 : ℝ)*base71 + (29449677549489/2632000000000000000000000000 : ℝ)*base74 + (4236597975014985131/658000000000000000000000000000000 : ℝ)*base75 + (3370325536725014869/658000000000000000000000000000000 : ℝ)*base78 + (223418788802985131/658000000000000000000000000000000 : ℝ)*base79 + (11787863185727/2632000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8042799/1000000000000000000000 : ℝ)*base89 + (8042799/1000000000000000000000 : ℝ)*base91 + (8042799/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41661/50000 : ℝ) ≤ (-34265014812528928502922058434141/41125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22950631/50000000000000 : ℝ)*(upper1) + (5720117/6250000000000 : ℝ)*(lower2) + (2793481/800000000000 : ℝ)*(upper3) + (562622659/100000000000000 : ℝ)*(upper5) + (1140543639132301/25000000000000 : ℝ)*(major0) + (1140543639132301/25000000000000 : ℝ)*(major1) + (1140543639132301/25000000000000 : ℝ)*(major2) + (6177269297/20000000000000 : ℝ)*(sp4) + (58381147839/20000000000000 : ℝ)*(sp6) + (269505238607/100000000000000 : ℝ)*(sp7) + (245401689988081/4000000000000 : ℝ)*(sp12) + (613507313604851/10000000000000 : ℝ)*(sp13) + (1226956246061863/20000000000000 : ℝ)*(sp14) + (1508389766711389/50000000000000 : ℝ)*(sp15) + (603409807732277/20000000000000 : ℝ)*(f.failure) + (613507313604851/10000000000000 : ℝ)*(f.sum) + (868709984377/658000000000000000000000000 : ℝ)*base65 + (2308913881611040547/164500000000000000000000000000000 : ℝ)*base67 + (769830210545540547/164500000000000000000000000000000 : ℝ)*base69 + (491324303275040547/164500000000000000000000000000000 : ℝ)*base71 + (2227769476741/658000000000000000000000000 : ℝ)*base73 + (1413221752678040547/164500000000000000000000000000000 : ℝ)*base75 + (384956705767540547/164500000000000000000000000000000 : ℝ)*base77 + (85060778913959453/164500000000000000000000000000000 : ℝ)*base80 + (6297748027029/658000000000000000000000000 : ℝ)*base81 + (3212497/2000000000000000000000 : ℝ)*base90 + (3212497/2000000000000000000000 : ℝ)*base92 + (3212497/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1231_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (20019/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41661/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1231_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1231_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (20019/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41661/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1231_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8423/2048 : ℝ) ≤ p) (hpb : p ≤ (1053/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151213139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59369/100000 : ℝ) else (20019/25000 : ℝ) ≤ X j i ∧ X j i ≤ (41661/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1231_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
