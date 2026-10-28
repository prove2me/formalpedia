-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:22.551872+00:00
-- url     : https://prove2.me/submissions/bf711c3b-7bc6-459c-a2ed-e12ad2e2d296

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
theorem support_rectangle_w1137_s0_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946697207/5000000000 : ℝ)*x 0 + (6055486487/10000000000 : ℝ)*x 1 + (1194959883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946697207/5000000000 : ℝ)^4165 ≤ (2201120707031/20000000000000 : ℝ)^3141 := by
    have hnat : (946697207 : ℕ)^4165*20000000000000^3141 ≤ 2201120707031^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946697207 5000000000 2201120707031 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6055486487/10000000000 : ℝ)^4165 ≤ (51419431178543/100000000000000 : ℝ)^3141 := by
    have hnat : (6055486487 : ℕ)^4165*100000000000000^3141 ≤ 51419431178543^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6055486487 10000000000 51419431178543 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194959883/2500000000 : ℝ)^4165 ≤ (18787482635197/50000000000000 : ℝ)^3141 := by
    have hnat : (1194959883 : ℕ)^4165*50000000000000^3141 ≤ 18787482635197^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194959883 2500000000 18787482635197 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946697207/5000000000 : ℝ), (6055486487/10000000000 : ℝ), (1194959883/2500000000 : ℝ)] ![(2201120707031/20000000000000 : ℝ), (51419431178543/100000000000000 : ℝ), (18787482635197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946697207/5000000000 : ℝ)|^4165 ≤ (2201120707031/20000000000000 : ℝ)^3141
        have hw : |(-946697207/5000000000 : ℝ)|=(946697207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6055486487/10000000000 : ℝ)|^4165 ≤ (51419431178543/100000000000000 : ℝ)^3141
        have hw : |(6055486487/10000000000 : ℝ)|=(6055486487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194959883/2500000000 : ℝ)|^4165 ≤ (18787482635197/50000000000000 : ℝ)^3141
        have hw : |(1194959883/2500000000 : ℝ)|=(1194959883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2758537471/5000000000 : ℝ)*x 0 + (-2625609269/10000000000 : ℝ)*x 1 + (149369991/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758537471/5000000000 : ℝ)^4165 ≤ (22723393421607/50000000000000 : ℝ)^3141 := by
    have hnat : (2758537471 : ℕ)^4165*50000000000000^3141 ≤ 22723393421607^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758537471 5000000000 22723393421607 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2625609269/10000000000 : ℝ)^4165 ≤ (4244561500201/25000000000000 : ℝ)^3141 := by
    have hnat : (2625609269 : ℕ)^4165*25000000000000^3141 ≤ 4244561500201^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625609269 10000000000 4244561500201 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149369991/312500000 : ℝ)^4165 ≤ (7514993429341/20000000000000 : ℝ)^3141 := by
    have hnat : (149369991 : ℕ)^4165*20000000000000^3141 ≤ 7514993429341^3141*312500000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149369991 312500000 7514993429341 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758537471/5000000000 : ℝ), (-2625609269/10000000000 : ℝ), (149369991/312500000 : ℝ)] ![(22723393421607/50000000000000 : ℝ), (4244561500201/25000000000000 : ℝ), (7514993429341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758537471/5000000000 : ℝ)|^4165 ≤ (22723393421607/50000000000000 : ℝ)^3141
        have hw : |(2758537471/5000000000 : ℝ)|=(2758537471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2625609269/10000000000 : ℝ)|^4165 ≤ (4244561500201/25000000000000 : ℝ)^3141
        have hw : |(-2625609269/10000000000 : ℝ)|=(2625609269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149369991/312500000 : ℝ)|^4165 ≤ (7514993429341/20000000000000 : ℝ)^3141
        have hw : |(149369991/312500000 : ℝ)|=(149369991/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5517075957/10000000000 : ℝ)*x 0 + (1194959821/2500000000 : ℝ)*x 1 + (-525121699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517075957/10000000000 : ℝ)^4165 ≤ (9089359586009/20000000000000 : ℝ)^3141 := by
    have hnat : (5517075957 : ℕ)^4165*20000000000000^3141 ≤ 9089359586009^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517075957 10000000000 9089359586009 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194959821/2500000000 : ℝ)^4165 ≤ (18787481342627/50000000000000 : ℝ)^3141 := by
    have hnat : (1194959821 : ℕ)^4165*50000000000000^3141 ≤ 18787481342627^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194959821 2500000000 18787481342627 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525121699/2000000000 : ℝ)^4165 ≤ (8489119682063/50000000000000 : ℝ)^3141 := by
    have hnat : (525121699 : ℕ)^4165*50000000000000^3141 ≤ 8489119682063^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525121699 2000000000 8489119682063 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517075957/10000000000 : ℝ), (1194959821/2500000000 : ℝ), (-525121699/2000000000 : ℝ)] ![(9089359586009/20000000000000 : ℝ), (18787481342627/50000000000000 : ℝ), (8489119682063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517075957/10000000000 : ℝ)|^4165 ≤ (9089359586009/20000000000000 : ℝ)^3141
        have hw : |(5517075957/10000000000 : ℝ)|=(5517075957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194959821/2500000000 : ℝ)|^4165 ≤ (18787481342627/50000000000000 : ℝ)^3141
        have hw : |(1194959821/2500000000 : ℝ)|=(1194959821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525121699/2000000000 : ℝ)|^4165 ≤ (8489119682063/50000000000000 : ℝ)^3141
        have hw : |(-525121699/2000000000 : ℝ)|=(525121699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050348919/2500000000 : ℝ)*x 0 + (3121310993/10000000000 : ℝ)*x 1 + (5656689173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050348919/2500000000 : ℝ)^4165 ≤ (1266705940533/4000000000000 : ℝ)^3141 := by
    have hnat : (1050348919 : ℕ)^4165*4000000000000^3141 ≤ 1266705940533^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050348919 2500000000 1266705940533 4000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121310993/10000000000 : ℝ)^4165 ≤ (10677152564029/50000000000000 : ℝ)^3141 := by
    have hnat : (3121310993 : ℕ)^4165*50000000000000^3141 ≤ 10677152564029^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121310993 10000000000 10677152564029 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5656689173/10000000000 : ℝ)^4165 ≤ (5872255792889/12500000000000 : ℝ)^3141 := by
    have hnat : (5656689173 : ℕ)^4165*12500000000000^3141 ≤ 5872255792889^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656689173 10000000000 5872255792889 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050348919/2500000000 : ℝ), (3121310993/10000000000 : ℝ), (5656689173/10000000000 : ℝ)] ![(1266705940533/4000000000000 : ℝ), (10677152564029/50000000000000 : ℝ), (5872255792889/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050348919/2500000000 : ℝ)|^4165 ≤ (1266705940533/4000000000000 : ℝ)^3141
        have hw : |(1050348919/2500000000 : ℝ)|=(1050348919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121310993/10000000000 : ℝ)|^4165 ≤ (10677152564029/50000000000000 : ℝ)^3141
        have hw : |(3121310993/10000000000 : ℝ)|=(3121310993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5656689173/10000000000 : ℝ)|^4165 ≤ (5872255792889/12500000000000 : ℝ)^3141
        have hw : |(5656689173/10000000000 : ℝ)|=(5656689173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-949277263/5000000000 : ℝ)*x 0 + (2406375061/5000000000 : ℝ)*x 1 + (3010709657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (949277263/5000000000 : ℝ)^4165 ≤ (11045393333757/100000000000000 : ℝ)^3141 := by
    have hnat : (949277263 : ℕ)^4165*100000000000000^3141 ≤ 11045393333757^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949277263 5000000000 11045393333757 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406375061/5000000000 : ℝ)^4165 ≤ (37918408065679/100000000000000 : ℝ)^3141 := by
    have hnat : (2406375061 : ℕ)^4165*100000000000000^3141 ≤ 37918408065679^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406375061 5000000000 37918408065679 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010709657/5000000000 : ℝ)^4165 ≤ (51036198583417/100000000000000 : ℝ)^3141 := by
    have hnat : (3010709657 : ℕ)^4165*100000000000000^3141 ≤ 51036198583417^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010709657 5000000000 51036198583417 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-949277263/5000000000 : ℝ), (2406375061/5000000000 : ℝ), (3010709657/5000000000 : ℝ)] ![(11045393333757/100000000000000 : ℝ), (37918408065679/100000000000000 : ℝ), (51036198583417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-949277263/5000000000 : ℝ)|^4165 ≤ (11045393333757/100000000000000 : ℝ)^3141
        have hw : |(-949277263/5000000000 : ℝ)|=(949277263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406375061/5000000000 : ℝ)|^4165 ≤ (37918408065679/100000000000000 : ℝ)^3141
        have hw : |(2406375061/5000000000 : ℝ)|=(2406375061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010709657/5000000000 : ℝ)|^4165 ≤ (51036198583417/100000000000000 : ℝ)^3141
        have hw : |(3010709657/5000000000 : ℝ)|=(3010709657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129261953/250000000 : ℝ)*x 0 + (-86501831/625000000 : ℝ)*x 1 + (3010709601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129261953/250000000 : ℝ)^4165 ≤ (10425061415351/25000000000000 : ℝ)^3141 := by
    have hnat : (129261953 : ℕ)^4165*25000000000000^3141 ≤ 10425061415351^3141*250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129261953 250000000 10425061415351 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86501831/625000000 : ℝ)^4165 ≤ (1815889248199/25000000000000 : ℝ)^3141 := by
    have hnat : (86501831 : ℕ)^4165*25000000000000^3141 ≤ 1815889248199^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86501831 625000000 1815889248199 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3010709601/5000000000 : ℝ)^4165 ≤ (12759049331163/25000000000000 : ℝ)^3141 := by
    have hnat : (3010709601 : ℕ)^4165*25000000000000^3141 ≤ 12759049331163^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3010709601 5000000000 12759049331163 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129261953/250000000 : ℝ), (-86501831/625000000 : ℝ), (3010709601/5000000000 : ℝ)] ![(10425061415351/25000000000000 : ℝ), (1815889248199/25000000000000 : ℝ), (12759049331163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129261953/250000000 : ℝ)|^4165 ≤ (10425061415351/25000000000000 : ℝ)^3141
        have hw : |(129261953/250000000 : ℝ)|=(129261953/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86501831/625000000 : ℝ)|^4165 ≤ (1815889248199/25000000000000 : ℝ)^3141
        have hw : |(-86501831/625000000 : ℝ)|=(86501831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3010709601/5000000000 : ℝ)|^4165 ≤ (12759049331163/25000000000000 : ℝ)^3141
        have hw : |(3010709601/5000000000 : ℝ)|=(3010709601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170478133/10000000000 : ℝ)*x 0 + (6021419213/10000000000 : ℝ)*x 1 + (-1384029259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170478133/10000000000 : ℝ)^4165 ≤ (41700245800431/100000000000000 : ℝ)^3141 := by
    have hnat : (5170478133 : ℕ)^4165*100000000000000^3141 ≤ 41700245800431^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170478133 10000000000 41700245800431 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6021419213/10000000000 : ℝ)^4165 ≤ (51036197448281/100000000000000 : ℝ)^3141 := by
    have hnat : (6021419213 : ℕ)^4165*100000000000000^3141 ≤ 51036197448281^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021419213 10000000000 51036197448281 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384029259/10000000000 : ℝ)^4165 ≤ (7263556735311/100000000000000 : ℝ)^3141 := by
    have hnat : (1384029259 : ℕ)^4165*100000000000000^3141 ≤ 7263556735311^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384029259 10000000000 7263556735311 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170478133/10000000000 : ℝ), (6021419213/10000000000 : ℝ), (-1384029259/10000000000 : ℝ)] ![(41700245800431/100000000000000 : ℝ), (51036197448281/100000000000000 : ℝ), (7263556735311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170478133/10000000000 : ℝ)|^4165 ≤ (41700245800431/100000000000000 : ℝ)^3141
        have hw : |(5170478133/10000000000 : ℝ)|=(5170478133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6021419213/10000000000 : ℝ)|^4165 ≤ (51036197448281/100000000000000 : ℝ)^3141
        have hw : |(6021419213/10000000000 : ℝ)|=(6021419213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1384029259/10000000000 : ℝ)|^4165 ≤ (7263556735311/100000000000000 : ℝ)^3141
        have hw : |(-1384029259/10000000000 : ℝ)|=(1384029259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s0_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842330377/2000000000 : ℝ)*x 0 + (5591278561/10000000000 : ℝ)*x 1 + (3189020821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842330377/2000000000 : ℝ)^4165 ≤ (15885098451937/50000000000000 : ℝ)^3141 := by
    have hnat : (842330377 : ℕ)^4165*50000000000000^3141 ≤ 15885098451937^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842330377 2000000000 15885098451937 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591278561/10000000000 : ℝ)^4165 ≤ (11564770892449/25000000000000 : ℝ)^3141 := by
    have hnat : (5591278561 : ℕ)^4165*25000000000000^3141 ≤ 11564770892449^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591278561 10000000000 11564770892449 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189020821/10000000000 : ℝ)^4165 ≤ (21970719510427/100000000000000 : ℝ)^3141 := by
    have hnat : (3189020821 : ℕ)^4165*100000000000000^3141 ≤ 21970719510427^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189020821 10000000000 21970719510427 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842330377/2000000000 : ℝ), (5591278561/10000000000 : ℝ), (3189020821/10000000000 : ℝ)] ![(15885098451937/50000000000000 : ℝ), (11564770892449/25000000000000 : ℝ), (21970719510427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842330377/2000000000 : ℝ)|^4165 ≤ (15885098451937/50000000000000 : ℝ)^3141
        have hw : |(842330377/2000000000 : ℝ)|=(842330377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591278561/10000000000 : ℝ)|^4165 ≤ (11564770892449/25000000000000 : ℝ)^3141
        have hw : |(5591278561/10000000000 : ℝ)|=(5591278561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189020821/10000000000 : ℝ)|^4165 ≤ (21970719510427/100000000000000 : ℝ)^3141
        have hw : |(3189020821/10000000000 : ℝ)|=(3189020821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13917/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8329/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8329 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8329*1^2048 ≤ 0^2048*1^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8329/2048 : ℝ) ≤ (300974684570913473/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8329 ≤ (300974684570913473/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8329*12500000000000000000^2048 ≤ 300974684570913473^2048*5^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 300974684570913473 12500000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (300974684570913473/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8329 := by
      have hnat : (1 : ℕ)^2048*1^8329 ≤ 1^8329*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12800974684570913473/12500000000000000000 : ℝ) ≤ (5029337377899387/5000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (12800974684570913473/12500000000000000000 : ℝ)^2048 ≤ (5029337377899387/5000000000000000 : ℝ)^8329 := by
      have hnat : (12800974684570913473 : ℕ)^2048*5000000000000000^8329 ≤ 5029337377899387^8329*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12800974684570913473 12500000000000000000 5029337377899387 5000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029337377899387/5000000000000000 : ℝ)) (X := (12800974684570913473/12500000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6550974684570913473/6250000000000000000 : ℝ) ≤ (2529337377899387/2500000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (6550974684570913473/6250000000000000000 : ℝ)^2048 ≤ (2529337377899387/2500000000000000 : ℝ)^8329 := by
      have hnat : (6550974684570913473 : ℕ)^2048*2500000000000000^8329 ≤ 2529337377899387^8329*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6550974684570913473 6250000000000000000 2529337377899387 2500000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529337377899387/2500000000000000 : ℝ)) (X := (6550974684570913473/6250000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29337377899387/2000000000000000 : ℝ)*(0 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29337377899387/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(300974684570913473/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29337377899387/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (1 : ℝ)+(29337377899387/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029337377899387/5000000000000000 : ℝ) by norm_num, show 1+(300974684570913473/12500000000000000000 : ℝ)+(0 : ℝ)=(12800974684570913473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(300974684570913473/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29337377899387/2000000000000000 : ℝ)*(2/5 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29337377899387/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529337377899387/2500000000000000 : ℝ) by norm_num, show 1+2*(300974684570913473/12500000000000000000 : ℝ)=(6550974684570913473/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29337377899387/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29337377899387/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29337377899387/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29337377899387/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29337377899387/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29337377899387/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-946697207/5000000000 : ℝ)*X 0 0+(6055486487/10000000000 : ℝ)*X 0 1+(1194959883/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2758537471/5000000000 : ℝ)*X 1 0+(-2625609269/10000000000 : ℝ)*X 1 1+(149369991/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517075957/10000000000 : ℝ)*X 2 0+(1194959821/2500000000 : ℝ)*X 2 1+(-525121699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050348919/2500000000 : ℝ)*X 0 0+(3121310993/10000000000 : ℝ)*X 0 1+(5656689173/10000000000 : ℝ)*X 0 2+(1050348919/2500000000 : ℝ)*X 1 0+(3121310993/10000000000 : ℝ)*X 1 1+(5656689173/10000000000 : ℝ)*X 1 2+(1050348919/2500000000 : ℝ)*X 2 0+(3121310993/10000000000 : ℝ)*X 2 1+(5656689173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-949277263/5000000000 : ℝ)*X 0 0+(2406375061/5000000000 : ℝ)*X 0 1+(3010709657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((129261953/250000000 : ℝ)*X 1 0+(-86501831/625000000 : ℝ)*X 1 1+(3010709601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170478133/10000000000 : ℝ)*X 2 0+(6021419213/10000000000 : ℝ)*X 2 1+(-1384029259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842330377/2000000000 : ℝ)*X 0 0+(5591278561/10000000000 : ℝ)*X 0 1+(3189020821/10000000000 : ℝ)*X 0 2+(842330377/2000000000 : ℝ)*X 1 0+(5591278561/10000000000 : ℝ)*X 1 1+(3189020821/10000000000 : ℝ)*X 1 2+(842330377/2000000000 : ℝ)*X 2 0+(5591278561/10000000000 : ℝ)*X 2 1+(3189020821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (353092153348322961528093/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26409749/100000000000000 : ℝ)*(base1) + (465856327/50000000000000 : ℝ)*(base19) + (467844237/50000000000000 : ℝ)*(base23) + (28049059/20000000000000 : ℝ)*(base24) + (29211333/12500000000000 : ℝ)*(upper3) + (589171095289329/100000000000000 : ℝ)*(major0) + (589171095289329/100000000000000 : ℝ)*(major1) + (589171095289329/100000000000000 : ℝ)*(major2) + (48994934597509/6250000000000 : ℝ)*(sp0) + (783920042550791/100000000000000 : ℝ)*(sp1) + (783919898329677/100000000000000 : ℝ)*(sp2) + (197209675359677/50000000000000 : ℝ)*(sp3) + (2047113051/100000000000000 : ℝ)*(sp4) + (1721488721/100000000000000 : ℝ)*(sp7) + (12325659331807/3125000000000 : ℝ)*(f.failure) + (391960487131723/50000000000000 : ℝ)*(f.sum) + (964222041323/100000000000000000000000000000 : ℝ)*base65 + (130731946141323/200000000000000000000000000000 : ℝ)*base67 + (323709744258677/200000000000000000000000000000 : ℝ)*base70 + (596952714541323/200000000000000000000000000000 : ℝ)*base71 + (164749705658677/100000000000000000000000000000 : ℝ)*base74 + (1889263741741323/200000000000000000000000000000 : ℝ)*base75 + (67373361141323/200000000000000000000000000000 : ℝ)*base77 + (605568962541323/200000000000000000000000000000 : ℝ)*base79 + (25108209941323/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1727927/312500000000000000000 : ℝ)*base89 + (1727927/312500000000000000000 : ℝ)*base91 + (1727927/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (321052444656999206375907/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11578059/25000000000000 : ℝ)*(base1) + (196555829/25000000000000 : ℝ)*(base19) + (31498307/4000000000000 : ℝ)*(base23) + (81630281/100000000000000 : ℝ)*(upper3) + (47288209/50000000000000 : ℝ)*(upper5) + (621815731768013/100000000000000 : ℝ)*(major0) + (621815731768013/100000000000000 : ℝ)*(major1) + (621815731768013/100000000000000 : ℝ)*(major2) + (390675931/25000000000000 : ℝ)*(sp1) + (1550081129/100000000000000 : ℝ)*(sp2) + (827356324126607/100000000000000 : ℝ)*(sp4) + (82735392888733/10000000000000 : ℝ)*(sp5) + (413676970137783/50000000000000 : ℝ)*(sp6) + (416275032391931/100000000000000 : ℝ)*(sp7) + (416275078704167/100000000000000 : ℝ)*(f.failure) + (827356277814371/100000000000000 : ℝ)*(f.sum) + (105662873608031/100000000000000000000000000000 : ℝ)*base65 + (112992069908031/200000000000000000000000000000 : ℝ)*base67 + (2133027050891969/200000000000000000000000000000 : ℝ)*base70 + (1023659169691969/200000000000000000000000000000 : ℝ)*base72 + (408344153408031/100000000000000000000000000000 : ℝ)*base73 + (1096790839108031/200000000000000000000000000000 : ℝ)*base75 + (432021194291969/200000000000000000000000000000 : ℝ)*base78 + (1707907041908031/200000000000000000000000000000 : ℝ)*base79 + (468832351291969/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21162887/10000000000000000000000 : ℝ)*base89 + (21162887/10000000000000000000000 : ℝ)*base91 + (21162887/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1137_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13917/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s1_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098422697/10000000000 : ℝ)*x 0 + (5702839427/10000000000 : ℝ)*x 1 + (5001225839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098422697/10000000000 : ℝ)^4165 ≤ (12613126304703/100000000000000 : ℝ)^3141 := by
    have hnat : (2098422697 : ℕ)^4165*100000000000000^3141 ≤ 12613126304703^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098422697 10000000000 12613126304703 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5702839427/10000000000 : ℝ)^4165 ≤ (23743471691923/50000000000000 : ℝ)^3141 := by
    have hnat : (5702839427 : ℕ)^4165*50000000000000^3141 ≤ 23743471691923^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5702839427 10000000000 23743471691923 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001225839/10000000000 : ℝ)^4165 ≤ (39899930292993/100000000000000 : ℝ)^3141 := by
    have hnat : (5001225839 : ℕ)^4165*100000000000000^3141 ≤ 39899930292993^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001225839 10000000000 39899930292993 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098422697/10000000000 : ℝ), (5702839427/10000000000 : ℝ), (5001225839/10000000000 : ℝ)] ![(12613126304703/100000000000000 : ℝ), (23743471691923/50000000000000 : ℝ), (39899930292993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098422697/10000000000 : ℝ)|^4165 ≤ (12613126304703/100000000000000 : ℝ)^3141
        have hw : |(-2098422697/10000000000 : ℝ)|=(2098422697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5702839427/10000000000 : ℝ)|^4165 ≤ (23743471691923/50000000000000 : ℝ)^3141
        have hw : |(5702839427/10000000000 : ℝ)|=(5702839427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001225839/10000000000 : ℝ)|^4165 ≤ (39899930292993/100000000000000 : ℝ)^3141
        have hw : |(5001225839/10000000000 : ℝ)|=(5001225839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270969777/500000000 : ℝ)*x 0 + (-99085923/400000000 : ℝ)*x 1 + (20004901/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270969777/500000000 : ℝ)^4165 ≤ (554786595993/1250000000000 : ℝ)^3141 := by
    have hnat : (270969777 : ℕ)^4165*1250000000000^3141 ≤ 554786595993^3141*500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270969777 500000000 554786595993 1250000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99085923/400000000 : ℝ)^4165 ≤ (491160882403/3125000000000 : ℝ)^3141 := by
    have hnat : (99085923 : ℕ)^4165*3125000000000^3141 ≤ 491160882403^3141*400000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99085923 400000000 491160882403 3125000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20004901/40000000 : ℝ)^4165 ≤ (39899924061989/100000000000000 : ℝ)^3141 := by
    have hnat : (20004901 : ℕ)^4165*100000000000000^3141 ≤ 39899924061989^3141*40000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20004901 40000000 39899924061989 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270969777/500000000 : ℝ), (-99085923/400000000 : ℝ), (20004901/40000000 : ℝ)] ![(554786595993/1250000000000 : ℝ), (491160882403/3125000000000 : ℝ), (39899924061989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270969777/500000000 : ℝ)|^4165 ≤ (554786595993/1250000000000 : ℝ)^3141
        have hw : |(270969777/500000000 : ℝ)|=(270969777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99085923/400000000 : ℝ)|^4165 ≤ (491160882403/3125000000000 : ℝ)^3141
        have hw : |(-99085923/400000000 : ℝ)|=(99085923/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20004901/40000000 : ℝ)|^4165 ≤ (39899924061989/100000000000000 : ℝ)^3141
        have hw : |(20004901/40000000 : ℝ)|=(20004901/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083879479/2000000000 : ℝ)*x 0 + (5001223597/10000000000 : ℝ)*x 1 + (-2477147761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083879479/2000000000 : ℝ)^4165 ≤ (22191473911961/50000000000000 : ℝ)^3141 := by
    have hnat : (1083879479 : ℕ)^4165*50000000000000^3141 ≤ 22191473911961^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083879479 2000000000 22191473911961 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001223597/10000000000 : ℝ)^4165 ≤ (39899906574979/100000000000000 : ℝ)^3141 := by
    have hnat : (5001223597 : ℕ)^4165*100000000000000^3141 ≤ 39899906574979^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001223597 10000000000 39899906574979 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2477147761/10000000000 : ℝ)^4165 ≤ (491160799847/3125000000000 : ℝ)^3141 := by
    have hnat : (2477147761 : ℕ)^4165*3125000000000^3141 ≤ 491160799847^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477147761 10000000000 491160799847 3125000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083879479/2000000000 : ℝ), (5001223597/10000000000 : ℝ), (-2477147761/10000000000 : ℝ)] ![(22191473911961/50000000000000 : ℝ), (39899906574979/100000000000000 : ℝ), (491160799847/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083879479/2000000000 : ℝ)|^4165 ≤ (22191473911961/50000000000000 : ℝ)^3141
        have hw : |(1083879479/2000000000 : ℝ)|=(1083879479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001223597/10000000000 : ℝ)|^4165 ≤ (39899906574979/100000000000000 : ℝ)^3141
        have hw : |(5001223597/10000000000 : ℝ)|=(5001223597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2477147761/10000000000 : ℝ)|^4165 ≤ (491160799847/3125000000000 : ℝ)^3141
        have hw : |(-2477147761/10000000000 : ℝ)|=(2477147761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158931757/5000000000 : ℝ)*x 0 + (147044449/400000000 : ℝ)*x 1 + (5070582103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158931757/5000000000 : ℝ)^4165 ≤ (32836936040173/100000000000000 : ℝ)^3141 := by
    have hnat : (2158931757 : ℕ)^4165*100000000000000^3141 ≤ 32836936040173^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158931757 5000000000 32836936040173 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147044449/400000000 : ℝ)^4165 ≤ (6631940860591/25000000000000 : ℝ)^3141 := by
    have hnat : (147044449 : ℕ)^4165*25000000000000^3141 ≤ 6631940860591^3141*400000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147044449 400000000 6631940860591 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5070582103/10000000000 : ℝ)^4165 ≤ (2031765024661/5000000000000 : ℝ)^3141 := by
    have hnat : (5070582103 : ℕ)^4165*5000000000000^3141 ≤ 2031765024661^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070582103 10000000000 2031765024661 5000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158931757/5000000000 : ℝ), (147044449/400000000 : ℝ), (5070582103/10000000000 : ℝ)] ![(32836936040173/100000000000000 : ℝ), (6631940860591/25000000000000 : ℝ), (2031765024661/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158931757/5000000000 : ℝ)|^4165 ≤ (32836936040173/100000000000000 : ℝ)^3141
        have hw : |(2158931757/5000000000 : ℝ)|=(2158931757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147044449/400000000 : ℝ)|^4165 ≤ (6631940860591/25000000000000 : ℝ)^3141
        have hw : |(147044449/400000000 : ℝ)|=(147044449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5070582103/10000000000 : ℝ)|^4165 ≤ (2031765024661/5000000000000 : ℝ)^3141
        have hw : |(5070582103/10000000000 : ℝ)|=(5070582103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099236103/10000000000 : ℝ)*x 0 + (501082371/1000000000 : ℝ)*x 1 + (5693050861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099236103/10000000000 : ℝ)^4165 ≤ (12619609836549/100000000000000 : ℝ)^3141 := by
    have hnat : (2099236103 : ℕ)^4165*100000000000000^3141 ≤ 12619609836549^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099236103 10000000000 12619609836549 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501082371/1000000000 : ℝ)^4165 ≤ (5000187185063/12500000000000 : ℝ)^3141 := by
    have hnat : (501082371 : ℕ)^4165*12500000000000^3141 ≤ 5000187185063^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501082371 1000000000 5000187185063 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5693050861/10000000000 : ℝ)^4165 ≤ (47378892669909/100000000000000 : ℝ)^3141 := by
    have hnat : (5693050861 : ℕ)^4165*100000000000000^3141 ≤ 47378892669909^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693050861 10000000000 47378892669909 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099236103/10000000000 : ℝ), (501082371/1000000000 : ℝ), (5693050861/10000000000 : ℝ)] ![(12619609836549/100000000000000 : ℝ), (5000187185063/12500000000000 : ℝ), (47378892669909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099236103/10000000000 : ℝ)|^4165 ≤ (12619609836549/100000000000000 : ℝ)^3141
        have hw : |(-2099236103/10000000000 : ℝ)|=(2099236103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501082371/1000000000 : ℝ)|^4165 ≤ (5000187185063/12500000000000 : ℝ)^3141
        have hw : |(501082371/1000000000 : ℝ)|=(501082371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5693050861/10000000000 : ℝ)|^4165 ≤ (47378892669909/100000000000000 : ℝ)^3141
        have hw : |(5693050861/10000000000 : ℝ)|=(5693050861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2619779883/5000000000 : ℝ)*x 0 + (-446330541/2500000000 : ℝ)*x 1 + (5693050557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619779883/5000000000 : ℝ)^4165 ≤ (2652539633621/6250000000000 : ℝ)^3141 := by
    have hnat : (2619779883 : ℕ)^4165*6250000000000^3141 ≤ 2652539633621^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619779883 5000000000 2652539633621 6250000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446330541/2500000000 : ℝ)^4165 ≤ (10180476534797/100000000000000 : ℝ)^3141 := by
    have hnat : (446330541 : ℕ)^4165*100000000000000^3141 ≤ 10180476534797^3141*2500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446330541 2500000000 10180476534797 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5693050557/10000000000 : ℝ)^4165 ≤ (11844722328789/25000000000000 : ℝ)^3141 := by
    have hnat : (5693050557 : ℕ)^4165*25000000000000^3141 ≤ 11844722328789^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693050557 10000000000 11844722328789 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619779883/5000000000 : ℝ), (-446330541/2500000000 : ℝ), (5693050557/10000000000 : ℝ)] ![(2652539633621/6250000000000 : ℝ), (10180476534797/100000000000000 : ℝ), (11844722328789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619779883/5000000000 : ℝ)|^4165 ≤ (2652539633621/6250000000000 : ℝ)^3141
        have hw : |(2619779883/5000000000 : ℝ)|=(2619779883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446330541/2500000000 : ℝ)|^4165 ≤ (10180476534797/100000000000000 : ℝ)^3141
        have hw : |(-446330541/2500000000 : ℝ)|=(446330541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5693050557/10000000000 : ℝ)|^4165 ≤ (11844722328789/25000000000000 : ℝ)^3141
        have hw : |(5693050557/10000000000 : ℝ)|=(5693050557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5239559821/10000000000 : ℝ)*x 0 + (711631343/1250000000 : ℝ)*x 1 + (-1785321813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239559821/10000000000 : ℝ)^4165 ≤ (10610158682169/25000000000000 : ℝ)^3141 := by
    have hnat : (5239559821 : ℕ)^4165*25000000000000^3141 ≤ 10610158682169^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239559821 10000000000 10610158682169 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711631343/1250000000 : ℝ)^4165 ≤ (4737889137877/10000000000000 : ℝ)^3141 := by
    have hnat : (711631343 : ℕ)^4165*10000000000000^3141 ≤ 4737889137877^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711631343 1250000000 4737889137877 10000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785321813/10000000000 : ℝ)^4165 ≤ (10180473880767/100000000000000 : ℝ)^3141 := by
    have hnat : (1785321813 : ℕ)^4165*100000000000000^3141 ≤ 10180473880767^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785321813 10000000000 10180473880767 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239559821/10000000000 : ℝ), (711631343/1250000000 : ℝ), (-1785321813/10000000000 : ℝ)] ![(10610158682169/25000000000000 : ℝ), (4737889137877/10000000000000 : ℝ), (10180473880767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239559821/10000000000 : ℝ)|^4165 ≤ (10610158682169/25000000000000 : ℝ)^3141
        have hw : |(5239559821/10000000000 : ℝ)|=(5239559821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(711631343/1250000000 : ℝ)|^4165 ≤ (4737889137877/10000000000000 : ℝ)^3141
        have hw : |(711631343/1250000000 : ℝ)|=(711631343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1785321813/10000000000 : ℝ)|^4165 ≤ (10180473880767/100000000000000 : ℝ)^3141
        have hw : |(-1785321813/10000000000 : ℝ)|=(1785321813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s1_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107986913/250000000 : ℝ)*x 0 + (5051507127/10000000000 : ℝ)*x 1 + (184778249/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107986913/250000000 : ℝ)^4165 ≤ (4106650360099/12500000000000 : ℝ)^3141 := by
    have hnat : (107986913 : ℕ)^4165*12500000000000^3141 ≤ 4106650360099^3141*250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107986913 250000000 4106650360099 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051507127/10000000000 : ℝ)^4165 ≤ (8086544701411/20000000000000 : ℝ)^3141 := by
    have hnat : (5051507127 : ℕ)^4165*20000000000000^3141 ≤ 8086544701411^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051507127 10000000000 8086544701411 20000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184778249/500000000 : ℝ)^4165 ≤ (6678518399413/25000000000000 : ℝ)^3141 := by
    have hnat : (184778249 : ℕ)^4165*25000000000000^3141 ≤ 6678518399413^3141*500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184778249 500000000 6678518399413 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107986913/250000000 : ℝ), (5051507127/10000000000 : ℝ), (184778249/500000000 : ℝ)] ![(4106650360099/12500000000000 : ℝ), (8086544701411/20000000000000 : ℝ), (6678518399413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107986913/250000000 : ℝ)|^4165 ≤ (4106650360099/12500000000000 : ℝ)^3141
        have hw : |(107986913/250000000 : ℝ)|=(107986913/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051507127/10000000000 : ℝ)|^4165 ≤ (8086544701411/20000000000000 : ℝ)^3141
        have hw : |(5051507127/10000000000 : ℝ)|=(5051507127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184778249/500000000 : ℝ)|^4165 ≤ (6678518399413/25000000000000 : ℝ)^3141
        have hw : |(184778249/500000000 : ℝ)|=(184778249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13917/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1023/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13917/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13917/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13917/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13917/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13917/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13917/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (393/100000 : ℝ) ^ (8329/2048 : ℝ) ≤ (257316861/1562500000000000000 : ℝ) := by
    have hpowers : (393/100000 : ℝ)^8329 ≤ (257316861/1562500000000000000 : ℝ)^2048 := by
      have hnat : (393 : ℕ)^8329*1562500000000000000^2048 ≤ 257316861^2048*100000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 100000 257316861 1562500000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/100000 : ℝ)) (X := (257316861/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13917/50000 : ℝ) ^ (8329/2048 : ℝ) ≤ (5509949751220667/1000000000000000000 : ℝ) := by
    have hpowers : (13917/50000 : ℝ)^8329 ≤ (5509949751220667/1000000000000000000 : ℝ)^2048 := by
      have hnat : (13917 : ℕ)^8329*1000000000000000000^2048 ≤ 5509949751220667^2048*50000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13917 50000 5509949751220667 1000000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13917/50000 : ℝ)) (X := (5509949751220667/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (781250000257316861/781250000000000000 : ℝ) ≤ (1000000000080987/1000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (781250000257316861/781250000000000000 : ℝ)^2048 ≤ (1000000000080987/1000000000000000 : ℝ)^8329 := by
      have hnat : (781250000257316861 : ℕ)^2048*1000000000000000^8329 ≤ 1000000000080987^8329*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781250000257316861 781250000000000000 1000000000080987 1000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000080987/1000000000000000 : ℝ)) (X := (781250000257316861/781250000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25137748747897586451/25000000000000000000 : ℝ) ≤ (10013520240965079/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (25137748747897586451/25000000000000000000 : ℝ)^2048 ≤ (10013520240965079/10000000000000000 : ℝ)^8329 := by
      have hnat : (25137748747897586451 : ℕ)^2048*10000000000000000^8329 ≤ 10013520240965079^8329*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25137748747897586451 25000000000000000000 10013520240965079 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013520240965079/10000000000000000 : ℝ)) (X := (25137748747897586451/25000000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (505509949751220667/500000000000000000 : ℝ) ≤ (313345015035009/312500000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (505509949751220667/500000000000000000 : ℝ)^2048 ≤ (313345015035009/312500000000000 : ℝ)^8329 := by
      have hnat : (505509949751220667 : ℕ)^2048*312500000000000^8329 ≤ 313345015035009^8329*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        505509949751220667 500000000000000000 313345015035009 312500000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313345015035009/312500000000000 : ℝ)) (X := (505509949751220667/500000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(257316861/1562500000000000000 : ℝ) ≤ ((7622204808707268011/7622500000000000000 : ℝ)+2*(4506746718403/914700000000000 : ℝ)*(393/100000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (7622204808707268011/7622500000000000000 : ℝ)+2*(4506746718403/914700000000000 : ℝ)*(393/100000 : ℝ)=(1000000000080987/1000000000000000 : ℝ) by norm_num, show 1+2*(257316861/1562500000000000000 : ℝ)=(781250000257316861/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5509949751220667/1000000000000000000 : ℝ)+(257316861/1562500000000000000 : ℝ) ≤ ((7622204808707268011/7622500000000000000 : ℝ)+(4506746718403/914700000000000 : ℝ)*((13917/50000 : ℝ)+(393/100000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (7622204808707268011/7622500000000000000 : ℝ)+(4506746718403/914700000000000 : ℝ)*((13917/50000 : ℝ)+(393/100000 : ℝ))=(10013520240965079/10000000000000000 : ℝ) by norm_num, show 1+(5509949751220667/1000000000000000000 : ℝ)+(257316861/1562500000000000000 : ℝ)=(25137748747897586451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5509949751220667/1000000000000000000 : ℝ) ≤ ((7622204808707268011/7622500000000000000 : ℝ)+2*(4506746718403/914700000000000 : ℝ)*(13917/50000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (7622204808707268011/7622500000000000000 : ℝ)+2*(4506746718403/914700000000000 : ℝ)*(13917/50000 : ℝ)=(313345015035009/312500000000000 : ℝ) by norm_num, show 1+2*(5509949751220667/1000000000000000000 : ℝ)=(505509949751220667/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7622204808707268011/7622500000000000000 : ℝ)*(X 1 0+X 2 0)+(4506746718403/914700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (393/100000 : ℝ)) (hi := (13917/50000 : ℝ)) (c := (7622204808707268011/7622500000000000000 : ℝ)) (alpha := (4506746718403/914700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7622204808707268011/7622500000000000000 : ℝ)*(X 0 1+X 2 1)+(4506746718403/914700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (393/100000 : ℝ)) (hi := (13917/50000 : ℝ)) (c := (7622204808707268011/7622500000000000000 : ℝ)) (alpha := (4506746718403/914700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7622204808707268011/7622500000000000000 : ℝ)*(X 0 2+X 1 2)+(4506746718403/914700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (393/100000 : ℝ)) (hi := (13917/50000 : ℝ)) (c := (7622204808707268011/7622500000000000000 : ℝ)) (alpha := (4506746718403/914700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2098422697/10000000000 : ℝ)*X 0 0+(5702839427/10000000000 : ℝ)*X 0 1+(5001225839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((270969777/500000000 : ℝ)*X 1 0+(-99085923/400000000 : ℝ)*X 1 1+(20004901/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083879479/2000000000 : ℝ)*X 2 0+(5001223597/10000000000 : ℝ)*X 2 1+(-2477147761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158931757/5000000000 : ℝ)*X 0 0+(147044449/400000000 : ℝ)*X 0 1+(5070582103/10000000000 : ℝ)*X 0 2+(2158931757/5000000000 : ℝ)*X 1 0+(147044449/400000000 : ℝ)*X 1 1+(5070582103/10000000000 : ℝ)*X 1 2+(2158931757/5000000000 : ℝ)*X 2 0+(147044449/400000000 : ℝ)*X 2 1+(5070582103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2099236103/10000000000 : ℝ)*X 0 0+(501082371/1000000000 : ℝ)*X 0 1+(5693050861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619779883/5000000000 : ℝ)*X 1 0+(-446330541/2500000000 : ℝ)*X 1 1+(5693050557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239559821/10000000000 : ℝ)*X 2 0+(711631343/1250000000 : ℝ)*X 2 1+(-1785321813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107986913/250000000 : ℝ)*X 0 0+(5051507127/10000000000 : ℝ)*X 0 1+(184778249/500000000 : ℝ)*X 0 2+(107986913/250000000 : ℝ)*X 1 0+(5051507127/10000000000 : ℝ)*X 1 1+(184778249/500000000 : ℝ)*X 1 2+(107986913/250000000 : ℝ)*X 2 0+(5051507127/10000000000 : ℝ)*X 2 1+(184778249/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (411520252280574496079218537/190562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136210619/100000000000000 : ℝ)*(base1) + (372842809/100000000000000 : ℝ)*(base19) + (613172009/100000000000000 : ℝ)*(base23) + (149809063/100000000000000 : ℝ)*(base37) + (132761457/100000000000000 : ℝ)*(lower2) + (1071200807541289/100000000000000 : ℝ)*(major0) + (1071200807541289/100000000000000 : ℝ)*(major1) + (1071200807541289/100000000000000 : ℝ)*(major2) + (142528487763427/10000000000000 : ℝ)*(sp0) + (1425284864434759/100000000000000 : ℝ)*(sp1) + (712642273547451/50000000000000 : ℝ)*(sp2) + (358558009900947/50000000000000 : ℝ)*(sp3) + (495853917/100000000000000 : ℝ)*(sp4) + (38505329/50000000000000 : ℝ)*(sp6) + (28684652232863/4000000000000 : ℝ)*(f.failure) + (11135040916231/781250000000 : ℝ)*(f.sum) + (48085007040829/22867500000000000000000000000 : ℝ)*base66 + (1668345941641606463/2286750000000000000000000000000000 : ℝ)*base68 + (4487411641374856463/2286750000000000000000000000000000 : ℝ)*base70 + (3718837183532893537/2286750000000000000000000000000000 : ℝ)*base71 + (26242555395977/11433750000000000000000000000 : ℝ)*base74 + (5094520173975106463/2286750000000000000000000000000000 : ℝ)*base76 + (15985121753031106463/2286750000000000000000000000000000 : ℝ)*base78 + (15529016138352106463/2286750000000000000000000000000000 : ℝ)*base80 + (42198224322443/45735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3021057/400000000000000000000 : ℝ)*base90 + (3021057/400000000000000000000 : ℝ)*base92 + (3021057/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191357507321139983265612117/23820312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (99604761/100000000000000 : ℝ)*(base1) + (1776260227/100000000000000 : ℝ)*(base19) + (226898553/12500000000000 : ℝ)*(base23) + (42360797/25000000000000 : ℝ)*(upper3) + (180086517/100000000000000 : ℝ)*(upper5) + (68852578798587/6250000000000 : ℝ)*(major0) + (68852578798587/6250000000000 : ℝ)*(major1) + (68852578798587/6250000000000 : ℝ)*(major2) + (893140341/12500000000000 : ℝ)*(sp1) + (7830939007/100000000000000 : ℝ)*(sp2) + (1465787659847979/100000000000000 : ℝ)*(sp4) + (183222329857533/12500000000000 : ℝ)*(sp5) + (1465777914115789/100000000000000 : ℝ)*(sp6) + (5899956751421/800000000000 : ℝ)*(sp7) + (147498938706477/20000000000000 : ℝ)*(f.failure) + (1465787560243219/100000000000000 : ℝ)*(f.sum) + (36083783924943/15245000000000000000000000000 : ℝ)*base66 + (16119633073967521/5955078125000000000000000000000 : ℝ)*base68 + (57896728307676791/23820312500000000000000000000000 : ℝ)*base69 + (209658895999099543/47640625000000000000000000000000 : ℝ)*base72 + (16829106077637/15245000000000000000000000000 : ℝ)*base73 + (239500278608412043/47640625000000000000000000000000 : ℝ)*base76 + (376373889753943293/47640625000000000000000000000000 : ℝ)*base78 + (651858806890880793/47640625000000000000000000000000 : ℝ)*base80 + (8438106128643/3811250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (94797/2000000000000000000000 : ℝ)*base89 + (94797/2000000000000000000000 : ℝ)*base91 + (94797/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1137_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13917/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1023/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1137_s2_0 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151920169/10000000000 : ℝ)*x 0 + (1102352307/2000000000 : ℝ)*x 1 + (2579145443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151920169/10000000000 : ℝ)^4165 ≤ (13041281248499/100000000000000 : ℝ)^3141 := by
    have hnat : (2151920169 : ℕ)^4165*100000000000000^3141 ≤ 13041281248499^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151920169 10000000000 13041281248499 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102352307/2000000000 : ℝ)^4165 ≤ (45388757687237/100000000000000 : ℝ)^3141 := by
    have hnat : (1102352307 : ℕ)^4165*100000000000000^3141 ≤ 45388757687237^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102352307 2000000000 45388757687237 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579145443/5000000000 : ℝ)^4165 ≤ (20784980521667/50000000000000 : ℝ)^3141 := by
    have hnat : (2579145443 : ℕ)^4165*50000000000000^3141 ≤ 20784980521667^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579145443 5000000000 20784980521667 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151920169/10000000000 : ℝ), (1102352307/2000000000 : ℝ), (2579145443/5000000000 : ℝ)] ![(13041281248499/100000000000000 : ℝ), (45388757687237/100000000000000 : ℝ), (20784980521667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151920169/10000000000 : ℝ)|^4165 ≤ (13041281248499/100000000000000 : ℝ)^3141
        have hw : |(-2151920169/10000000000 : ℝ)|=(2151920169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102352307/2000000000 : ℝ)|^4165 ≤ (45388757687237/100000000000000 : ℝ)^3141
        have hw : |(1102352307/2000000000 : ℝ)|=(1102352307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579145443/5000000000 : ℝ)|^4165 ≤ (20784980521667/50000000000000 : ℝ)^3141
        have hw : |(2579145443/5000000000 : ℝ)|=(2579145443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_1 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687039791/5000000000 : ℝ)*x 0 + (-2335725617/10000000000 : ℝ)*x 1 + (644786599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687039791/5000000000 : ℝ)^4165 ≤ (21945744203941/50000000000000 : ℝ)^3141 := by
    have hnat : (2687039791 : ℕ)^4165*50000000000000^3141 ≤ 21945744203941^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687039791 5000000000 21945744203941 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2335725617/10000000000 : ℝ)^4165 ≤ (14538530165393/100000000000000 : ℝ)^3141 := by
    have hnat : (2335725617 : ℕ)^4165*100000000000000^3141 ≤ 14538530165393^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335725617 10000000000 14538530165393 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644786599/1250000000 : ℝ)^4165 ≤ (20784990705559/50000000000000 : ℝ)^3141 := by
    have hnat : (644786599 : ℕ)^4165*50000000000000^3141 ≤ 20784990705559^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644786599 1250000000 20784990705559 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687039791/5000000000 : ℝ), (-2335725617/10000000000 : ℝ), (644786599/1250000000 : ℝ)] ![(21945744203941/50000000000000 : ℝ), (14538530165393/100000000000000 : ℝ), (20784990705559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687039791/5000000000 : ℝ)|^4165 ≤ (21945744203941/50000000000000 : ℝ)^3141
        have hw : |(2687039791/5000000000 : ℝ)|=(2687039791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2335725617/10000000000 : ℝ)|^4165 ≤ (14538530165393/100000000000000 : ℝ)^3141
        have hw : |(-2335725617/10000000000 : ℝ)|=(2335725617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644786599/1250000000 : ℝ)|^4165 ≤ (20784990705559/50000000000000 : ℝ)^3141
        have hw : |(644786599/1250000000 : ℝ)|=(644786599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_2 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374079541/10000000000 : ℝ)*x 0 + (5158292723/10000000000 : ℝ)*x 1 + (-7299143/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374079541/10000000000 : ℝ)^4165 ≤ (43891487963857/100000000000000 : ℝ)^3141 := by
    have hnat : (5374079541 : ℕ)^4165*100000000000000^3141 ≤ 43891487963857^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374079541 10000000000 43891487963857 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158292723/10000000000 : ℝ)^4165 ≤ (1662799226951/4000000000000 : ℝ)^3141 := by
    have hnat : (5158292723 : ℕ)^4165*4000000000000^3141 ≤ 1662799226951^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158292723 10000000000 1662799226951 4000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7299143/31250000 : ℝ)^4165 ≤ (56791138069/390625000000 : ℝ)^3141 := by
    have hnat : (7299143 : ℕ)^4165*390625000000^3141 ≤ 56791138069^3141*31250000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7299143 31250000 56791138069 390625000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374079541/10000000000 : ℝ), (5158292723/10000000000 : ℝ), (-7299143/31250000 : ℝ)] ![(43891487963857/100000000000000 : ℝ), (1662799226951/4000000000000 : ℝ), (56791138069/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374079541/10000000000 : ℝ)|^4165 ≤ (43891487963857/100000000000000 : ℝ)^3141
        have hw : |(5374079541/10000000000 : ℝ)|=(5374079541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158292723/10000000000 : ℝ)|^4165 ≤ (1662799226951/4000000000000 : ℝ)^3141
        have hw : |(5158292723/10000000000 : ℝ)|=(5158292723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7299143/31250000 : ℝ)|^4165 ≤ (56791138069/390625000000 : ℝ)^3141
        have hw : |(-7299143/31250000 : ℝ)|=(7299143/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_3 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354553597/10000000000 : ℝ)*x 0 + (2008673293/5000000000 : ℝ)*x 1 + (2359936579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354553597/10000000000 : ℝ)^4165 ≤ (33207437107629/100000000000000 : ℝ)^3141 := by
    have hnat : (4354553597 : ℕ)^4165*100000000000000^3141 ≤ 33207437107629^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354553597 10000000000 33207437107629 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008673293/5000000000 : ℝ)^4165 ≤ (1865087636631/6250000000000 : ℝ)^3141 := by
    have hnat : (2008673293 : ℕ)^4165*6250000000000^3141 ≤ 1865087636631^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008673293 5000000000 1865087636631 6250000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2359936579/5000000000 : ℝ)^4165 ≤ (18475580344727/50000000000000 : ℝ)^3141 := by
    have hnat : (2359936579 : ℕ)^4165*50000000000000^3141 ≤ 18475580344727^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359936579 5000000000 18475580344727 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354553597/10000000000 : ℝ), (2008673293/5000000000 : ℝ), (2359936579/5000000000 : ℝ)] ![(33207437107629/100000000000000 : ℝ), (1865087636631/6250000000000 : ℝ), (18475580344727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354553597/10000000000 : ℝ)|^4165 ≤ (33207437107629/100000000000000 : ℝ)^3141
        have hw : |(4354553597/10000000000 : ℝ)|=(4354553597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008673293/5000000000 : ℝ)|^4165 ≤ (1865087636631/6250000000000 : ℝ)^3141
        have hw : |(2008673293/5000000000 : ℝ)|=(2008673293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2359936579/5000000000 : ℝ)|^4165 ≤ (18475580344727/50000000000000 : ℝ)^3141
        have hw : |(2359936579/5000000000 : ℝ)|=(2359936579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_4 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076012099/5000000000 : ℝ)*x 0 + (5160736977/10000000000 : ℝ)*x 1 + (688661351/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076012099/5000000000 : ℝ)^4165 ≤ (13042117234529/100000000000000 : ℝ)^3141 := by
    have hnat : (1076012099 : ℕ)^4165*100000000000000^3141 ≤ 13042117234529^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076012099 5000000000 13042117234529 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160736977/10000000000 : ℝ)^4165 ≤ (10399025583599/25000000000000 : ℝ)^3141 := by
    have hnat : (5160736977 : ℕ)^4165*25000000000000^3141 ≤ 10399025583599^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160736977 10000000000 10399025583599 25000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688661351/1250000000 : ℝ)^4165 ≤ (1134044510477/2500000000000 : ℝ)^3141 := by
    have hnat : (688661351 : ℕ)^4165*2500000000000^3141 ≤ 1134044510477^3141*1250000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688661351 1250000000 1134044510477 2500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076012099/5000000000 : ℝ), (5160736977/10000000000 : ℝ), (688661351/1250000000 : ℝ)] ![(13042117234529/100000000000000 : ℝ), (10399025583599/25000000000000 : ℝ), (1134044510477/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076012099/5000000000 : ℝ)|^4165 ≤ (13042117234529/100000000000000 : ℝ)^3141
        have hw : |(-1076012099/5000000000 : ℝ)|=(1076012099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160736977/10000000000 : ℝ)|^4165 ≤ (10399025583599/25000000000000 : ℝ)^3141
        have hw : |(5160736977/10000000000 : ℝ)|=(5160736977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688661351/1250000000 : ℝ)|^4165 ≤ (1134044510477/2500000000000 : ℝ)^3141
        have hw : |(688661351/1250000000 : ℝ)|=(688661351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_5 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330276539/625000000 : ℝ)*x 0 + (-396945131/2000000000 : ℝ)*x 1 + (68866143/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330276539/625000000 : ℝ)^4165 ≤ (21461593571467/50000000000000 : ℝ)^3141 := by
    have hnat : (330276539 : ℕ)^4165*50000000000000^3141 ≤ 21461593571467^3141*625000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330276539 625000000 21461593571467 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396945131/2000000000 : ℝ)^4165 ≤ (11715025521203/100000000000000 : ℝ)^3141 := by
    have hnat : (396945131 : ℕ)^4165*100000000000000^3141 ≤ 11715025521203^3141*2000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396945131 2000000000 11715025521203 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68866143/125000000 : ℝ)^4165 ≤ (45361787319231/100000000000000 : ℝ)^3141 := by
    have hnat : (68866143 : ℕ)^4165*100000000000000^3141 ≤ 45361787319231^3141*125000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68866143 125000000 45361787319231 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330276539/625000000 : ℝ), (-396945131/2000000000 : ℝ), (68866143/125000000 : ℝ)] ![(21461593571467/50000000000000 : ℝ), (11715025521203/100000000000000 : ℝ), (45361787319231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330276539/625000000 : ℝ)|^4165 ≤ (21461593571467/50000000000000 : ℝ)^3141
        have hw : |(330276539/625000000 : ℝ)|=(330276539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396945131/2000000000 : ℝ)|^4165 ≤ (11715025521203/100000000000000 : ℝ)^3141
        have hw : |(-396945131/2000000000 : ℝ)|=(396945131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68866143/125000000 : ℝ)|^4165 ≤ (45361787319231/100000000000000 : ℝ)^3141
        have hw : |(68866143/125000000 : ℝ)|=(68866143/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_6 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528442321/1000000000 : ℝ)*x 0 + (2754645631/5000000000 : ℝ)*x 1 + (-39694557/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528442321/1000000000 : ℝ)^4165 ≤ (5365396489157/12500000000000 : ℝ)^3141 := by
    have hnat : (528442321 : ℕ)^4165*12500000000000^3141 ≤ 5365396489157^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528442321 1000000000 5365396489157 12500000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754645631/5000000000 : ℝ)^4165 ≤ (22680892687917/50000000000000 : ℝ)^3141 := by
    have hnat : (2754645631 : ℕ)^4165*50000000000000^3141 ≤ 22680892687917^3141*5000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754645631 5000000000 22680892687917 50000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39694557/200000000 : ℝ)^4165 ≤ (11715042701253/100000000000000 : ℝ)^3141 := by
    have hnat : (39694557 : ℕ)^4165*100000000000000^3141 ≤ 11715042701253^3141*200000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39694557 200000000 11715042701253 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528442321/1000000000 : ℝ), (2754645631/5000000000 : ℝ), (-39694557/200000000 : ℝ)] ![(5365396489157/12500000000000 : ℝ), (22680892687917/50000000000000 : ℝ), (11715042701253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528442321/1000000000 : ℝ)|^4165 ≤ (5365396489157/12500000000000 : ℝ)^3141
        have hw : |(528442321/1000000000 : ℝ)|=(528442321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754645631/5000000000 : ℝ)|^4165 ≤ (22680892687917/50000000000000 : ℝ)^3141
        have hw : |(2754645631/5000000000 : ℝ)|=(2754645631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39694557/200000000 : ℝ)|^4165 ≤ (11715042701253/100000000000000 : ℝ)^3141
        have hw : |(-39694557/200000000 : ℝ)|=(39694557/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1137_s2_7 (p : ℝ) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354759621/10000000000 : ℝ)*x 0 + (471501311/1000000000 : ℝ)*x 1 + (201112773/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354759621/10000000000 : ℝ)^4165 ≤ (33209520446667/100000000000000 : ℝ)^3141 := by
    have hnat : (4354759621 : ℕ)^4165*100000000000000^3141 ≤ 33209520446667^3141*10000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354759621 10000000000 33209520446667 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471501311/1000000000 : ℝ)^4165 ≤ (36900716346769/100000000000000 : ℝ)^3141 := by
    have hnat : (471501311 : ℕ)^4165*100000000000000^3141 ≤ 36900716346769^3141*1000000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471501311 1000000000 36900716346769 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201112773/500000000 : ℝ)^4165 ≤ (29889763194647/100000000000000 : ℝ)^3141 := by
    have hnat : (201112773 : ℕ)^4165*100000000000000^3141 ≤ 29889763194647^3141*500000000^4165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201112773 500000000 29889763194647 100000000000000 4165 3141 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4165/1024 : ℝ)) 4165 3141 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354759621/10000000000 : ℝ), (471501311/1000000000 : ℝ), (201112773/500000000 : ℝ)] ![(33209520446667/100000000000000 : ℝ), (36900716346769/100000000000000 : ℝ), (29889763194647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354759621/10000000000 : ℝ)|^4165 ≤ (33209520446667/100000000000000 : ℝ)^3141
        have hw : |(4354759621/10000000000 : ℝ)|=(4354759621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(471501311/1000000000 : ℝ)|^4165 ≤ (36900716346769/100000000000000 : ℝ)^3141
        have hw : |(471501311/1000000000 : ℝ)|=(471501311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201112773/500000000 : ℝ)|^4165 ≤ (29889763194647/100000000000000 : ℝ)^3141
        have hw : |(201112773/500000000 : ℝ)|=(201112773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1137_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1023/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1131/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16517/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1023/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1023/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1023/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1023/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1023/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1023/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/50000 : ℝ) ^ (8329/2048 : ℝ) ≤ (5150126733773/625000000000000000 : ℝ) := by
    have hpowers : (2811/50000 : ℝ)^8329 ≤ (5150126733773/625000000000000000 : ℝ)^2048 := by
      have hnat : (2811 : ℕ)^8329*625000000000000000^2048 ≤ 5150126733773^2048*50000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 50000 5150126733773 625000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/50000 : ℝ)) (X := (5150126733773/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1023/5000 : ℝ) ^ (8329/2048 : ℝ) ≤ (19698623772217701/12500000000000000000 : ℝ) := by
    have hpowers : (1023/5000 : ℝ)^8329 ≤ (19698623772217701/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1023 : ℕ)^8329*12500000000000000000^2048 ≤ 19698623772217701^2048*5000^8329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1023 5000 19698623772217701 12500000000000000000 8329 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1023/5000 : ℝ)) (X := (19698623772217701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (312505150126733773/312500000000000000 : ℝ) ≤ (10000040523064989/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (312505150126733773/312500000000000000 : ℝ)^2048 ≤ (10000040523064989/10000000000000000 : ℝ)^8329 := by
      have hnat : (312505150126733773 : ℕ)^2048*10000000000000000^8329 ≤ 10000040523064989^8329*312500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312505150126733773 312500000000000000 10000040523064989 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000040523064989/10000000000000000 : ℝ)) (X := (312505150126733773/312500000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12519801626306893161/12500000000000000000 : ℝ) ≤ (10003892859177059/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (12519801626306893161/12500000000000000000 : ℝ)^2048 ≤ (10003892859177059/10000000000000000 : ℝ)^8329 := by
      have hnat : (12519801626306893161 : ℕ)^2048*10000000000000000^8329 ≤ 10003892859177059^8329*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519801626306893161 12500000000000000000 10003892859177059 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003892859177059/10000000000000000 : ℝ)) (X := (12519801626306893161/12500000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6269698623772217701/6250000000000000000 : ℝ) ≤ (10007745195289129/10000000000000000 : ℝ) ^ (8329/2048 : ℝ) := by
    have hpowers : (6269698623772217701/6250000000000000000 : ℝ)^2048 ≤ (10007745195289129/10000000000000000 : ℝ)^8329 := by
      have hnat : (6269698623772217701 : ℕ)^2048*10000000000000000^8329 ≤ 10007745195289129^8329*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6269698623772217701 6250000000000000000 10007745195289129 10000000000000000 2048 8329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007745195289129/10000000000000000 : ℝ)) (X := (6269698623772217701/6250000000000000000 : ℝ)) (by norm_num) 8329 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5150126733773/625000000000000000 : ℝ) ≤ ((24722880935665698617/24730000000000000000 : ℝ)+2*(385233611207/148380000000000 : ℝ)*(2811/50000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (24722880935665698617/24730000000000000000 : ℝ)+2*(385233611207/148380000000000 : ℝ)*(2811/50000 : ℝ)=(10000040523064989/10000000000000000 : ℝ) by norm_num, show 1+2*(5150126733773/625000000000000000 : ℝ)=(312505150126733773/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19698623772217701/12500000000000000000 : ℝ)+(5150126733773/625000000000000000 : ℝ) ≤ ((24722880935665698617/24730000000000000000 : ℝ)+(385233611207/148380000000000 : ℝ)*((1023/5000 : ℝ)+(2811/50000 : ℝ)))^(8329/2048 : ℝ) := by
    rw [show (24722880935665698617/24730000000000000000 : ℝ)+(385233611207/148380000000000 : ℝ)*((1023/5000 : ℝ)+(2811/50000 : ℝ))=(10003892859177059/10000000000000000 : ℝ) by norm_num, show 1+(19698623772217701/12500000000000000000 : ℝ)+(5150126733773/625000000000000000 : ℝ)=(12519801626306893161/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19698623772217701/12500000000000000000 : ℝ) ≤ ((24722880935665698617/24730000000000000000 : ℝ)+2*(385233611207/148380000000000 : ℝ)*(1023/5000 : ℝ))^(8329/2048 : ℝ) := by
    rw [show (24722880935665698617/24730000000000000000 : ℝ)+2*(385233611207/148380000000000 : ℝ)*(1023/5000 : ℝ)=(10007745195289129/10000000000000000 : ℝ) by norm_num, show 1+2*(19698623772217701/12500000000000000000 : ℝ)=(6269698623772217701/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24722880935665698617/24730000000000000000 : ℝ)*(X 1 0+X 2 0)+(385233611207/148380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2811/50000 : ℝ)) (hi := (1023/5000 : ℝ)) (c := (24722880935665698617/24730000000000000000 : ℝ)) (alpha := (385233611207/148380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24722880935665698617/24730000000000000000 : ℝ)*(X 0 1+X 2 1)+(385233611207/148380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2811/50000 : ℝ)) (hi := (1023/5000 : ℝ)) (c := (24722880935665698617/24730000000000000000 : ℝ)) (alpha := (385233611207/148380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24722880935665698617/24730000000000000000 : ℝ)*(X 0 2+X 1 2)+(385233611207/148380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8329/2048 : ℝ)) (lo := (2811/50000 : ℝ)) (hi := (1023/5000 : ℝ)) (c := (24722880935665698617/24730000000000000000 : ℝ)) (alpha := (385233611207/148380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151920169/10000000000 : ℝ)*X 0 0+(1102352307/2000000000 : ℝ)*X 0 1+(2579145443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687039791/5000000000 : ℝ)*X 1 0+(-2335725617/10000000000 : ℝ)*X 1 1+(644786599/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374079541/10000000000 : ℝ)*X 2 0+(5158292723/10000000000 : ℝ)*X 2 1+(-7299143/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354553597/10000000000 : ℝ)*X 0 0+(2008673293/5000000000 : ℝ)*X 0 1+(2359936579/5000000000 : ℝ)*X 0 2+(4354553597/10000000000 : ℝ)*X 1 0+(2008673293/5000000000 : ℝ)*X 1 1+(2359936579/5000000000 : ℝ)*X 1 2+(4354553597/10000000000 : ℝ)*X 2 0+(2008673293/5000000000 : ℝ)*X 2 1+(2359936579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076012099/5000000000 : ℝ)*X 0 0+(5160736977/10000000000 : ℝ)*X 0 1+(688661351/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330276539/625000000 : ℝ)*X 1 0+(-396945131/2000000000 : ℝ)*X 1 1+(68866143/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528442321/1000000000 : ℝ)*X 2 0+(2754645631/5000000000 : ℝ)*X 2 1+(-39694557/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354759621/10000000000 : ℝ)*X 0 0+(471501311/1000000000 : ℝ)*X 0 1+(201112773/500000000 : ℝ)*X 0 2+(4354759621/10000000000 : ℝ)*X 1 0+(471501311/1000000000 : ℝ)*X 1 1+(201112773/500000000 : ℝ)*X 1 2+(4354759621/10000000000 : ℝ)*X 2 0+(471501311/1000000000 : ℝ)*X 2 1+(201112773/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1137_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1710976501186629574332627143/618250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63619293/50000000000000 : ℝ)*(base15) + (93980719/100000000000000 : ℝ)*(base29) + (7274391/5000000000000 : ℝ)*(upper2) + (48377103/100000000000000 : ℝ)*(upper3) + (37514449/50000000000000 : ℝ)*(upper4) + (1063137432091187/50000000000000 : ℝ)*(major0) + (2126274958163093/100000000000000 : ℝ)*(major1) + (2126274958163093/100000000000000 : ℝ)*(major2) + (282910247653731/10000000000000 : ℝ)*(sp0) + (2829112995618957/100000000000000 : ℝ)*(sp1) + (353639140357193/12500000000000 : ℝ)*(sp2) + (711717650650039/50000000000000 : ℝ)*(sp3) + (10740300953/100000000000000 : ℝ)*(sp4) + (52237579/4000000000000 : ℝ)*(sp7) + (711718303619777/50000000000000 : ℝ)*(f.failure) + (2829113216838263/100000000000000 : ℝ)*(f.sum) + (3386066335721/927375000000000000000000000 : ℝ)*base65 + (11437761767253872857/7419000000000000000000000000000000 : ℝ)*base68 + (6764723734614872857/7419000000000000000000000000000000 : ℝ)*base70 + (50457418851731615137/3709500000000000000000000000000000 : ℝ)*base71 + (15181372163629/4946000000000000000000000000 : ℝ)*base73 + (8672137281471372857/7419000000000000000000000000000000 : ℝ)*base76 + (2967064746903384863/3709500000000000000000000000000000 : ℝ)*base78 + (41032001350809372857/7419000000000000000000000000000000 : ℝ)*base80 + (37428347140959/4946000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (41936097/5000000000000000000000 : ℝ)*base89 + (41936097/5000000000000000000000 : ℝ)*base91 + (41936097/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110857611455542354305442999/30912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52793693/12500000000000 : ℝ)*(base19) + (350579/625000000000 : ℝ)*(base23) + (162068229/50000000000000 : ℝ)*(upper2) + (134892501/100000000000000 : ℝ)*(upper3) + (107812582378849/5000000000000 : ℝ)*(major0) + (107812582378849/5000000000000 : ℝ)*(major1) + (107812582378849/5000000000000 : ℝ)*(major2) + (5766634141/100000000000000 : ℝ)*(sp0) + (780811231/6250000000000 : ℝ)*(sp1) + (17002799/25000000000000 : ℝ)*(sp3) + (2868992881121653/100000000000000 : ℝ)*(sp4) + (1434492866213277/50000000000000 : ℝ)*(sp5) + (1434499295831577/50000000000000 : ℝ)*(sp6) + (90219028740489/6250000000000 : ℝ)*(sp7) + (72175226392951/5000000000000 : ℝ)*(f.failure) + (1434499323877897/50000000000000 : ℝ)*(f.sum) + (12900496612393/7419000000000000000000000000 : ℝ)*base65 + (1139178386986844501/370950000000000000000000000000000 : ℝ)*base68 + (1862909866570544501/370950000000000000000000000000000 : ℝ)*base70 + (551534447170244501/370950000000000000000000000000000 : ℝ)*base72 + (2548237864787/3709500000000000000000000000 : ℝ)*base73 + (1432846922330444501/370950000000000000000000000000000 : ℝ)*base76 + (1907791291803644501/370950000000000000000000000000000 : ℝ)*base78 + (446435913787755499/370950000000000000000000000000000 : ℝ)*base79 + (19857989413/463687500000000000000000000 : ℝ)*base81 + (2158889/500000000000000000000 : ℝ)*base90 + (2158889/500000000000000000000 : ℝ)*base92 + (2158889/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1137_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1023/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1137_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1137_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1137_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1137_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1137_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8329/2048 : ℝ) ≤ p) (hpb : p ≤ (4165/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149376161/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16517/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1137_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
