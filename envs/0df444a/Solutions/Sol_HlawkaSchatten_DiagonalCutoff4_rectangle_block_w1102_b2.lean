-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:37.447904+00:00
-- url     : https://prove2.me/submissions/c9fab50b-22f0-4244-9244-66b1b2577f76

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
theorem support_rectangle_w1102_s6_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093061343/5000000000 : ℝ)*x 0 + (215767541/400000000 : ℝ)*x 1 + (2632328841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093061343/5000000000 : ℝ)^8295 ≤ (3319977802313/25000000000000 : ℝ)^6247 := by
    have hnat : (1093061343 : ℕ)^8295*25000000000000^6247 ≤ 3319977802313^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093061343 5000000000 3319977802313 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215767541/400000000 : ℝ)^8295 ≤ (137686547197/312500000000 : ℝ)^6247 := by
    have hnat : (215767541 : ℕ)^8295*312500000000^6247 ≤ 137686547197^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215767541 400000000 137686547197 312500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632328841/5000000000 : ℝ)^8295 ≤ (21330196835397/50000000000000 : ℝ)^6247 := by
    have hnat : (2632328841 : ℕ)^8295*50000000000000^6247 ≤ 21330196835397^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632328841 5000000000 21330196835397 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093061343/5000000000 : ℝ), (215767541/400000000 : ℝ), (2632328841/5000000000 : ℝ)] ![(3319977802313/25000000000000 : ℝ), (137686547197/312500000000 : ℝ), (21330196835397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093061343/5000000000 : ℝ)|^8295 ≤ (3319977802313/25000000000000 : ℝ)^6247
        have hw : |(-1093061343/5000000000 : ℝ)|=(1093061343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215767541/400000000 : ℝ)|^8295 ≤ (137686547197/312500000000 : ℝ)^6247
        have hw : |(215767541/400000000 : ℝ)|=(215767541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632328841/5000000000 : ℝ)|^8295 ≤ (21330196835397/50000000000000 : ℝ)^6247
        have hw : |(2632328841/5000000000 : ℝ)|=(2632328841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668125141/1250000000 : ℝ)*x 0 + (-2251839633/10000000000 : ℝ)*x 1 + (5264657641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668125141/1250000000 : ℝ)^8295 ≤ (43527019103787/100000000000000 : ℝ)^6247 := by
    have hnat : (668125141 : ℕ)^8295*100000000000000^6247 ≤ 43527019103787^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668125141 1250000000 43527019103787 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251839633/10000000000 : ℝ)^8295 ≤ (13812587653469/100000000000000 : ℝ)^6247 := by
    have hnat : (2251839633 : ℕ)^8295*100000000000000^6247 ≤ 13812587653469^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251839633 10000000000 13812587653469 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264657641/10000000000 : ℝ)^8295 ≤ (42660393229647/100000000000000 : ℝ)^6247 := by
    have hnat : (5264657641 : ℕ)^8295*100000000000000^6247 ≤ 42660393229647^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264657641 10000000000 42660393229647 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668125141/1250000000 : ℝ), (-2251839633/10000000000 : ℝ), (5264657641/10000000000 : ℝ)] ![(43527019103787/100000000000000 : ℝ), (13812587653469/100000000000000 : ℝ), (42660393229647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668125141/1250000000 : ℝ)|^8295 ≤ (43527019103787/100000000000000 : ℝ)^6247
        have hw : |(668125141/1250000000 : ℝ)|=(668125141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251839633/10000000000 : ℝ)|^8295 ≤ (13812587653469/100000000000000 : ℝ)^6247
        have hw : |(-2251839633/10000000000 : ℝ)|=(2251839633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264657641/10000000000 : ℝ)|^8295 ≤ (42660393229647/100000000000000 : ℝ)^6247
        have hw : |(5264657641/10000000000 : ℝ)|=(5264657641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345001161/10000000000 : ℝ)*x 0 + (131616441/250000000 : ℝ)*x 1 + (-2251839591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345001161/10000000000 : ℝ)^8295 ≤ (2720438716289/6250000000000 : ℝ)^6247 := by
    have hnat : (5345001161 : ℕ)^8295*6250000000000^6247 ≤ 2720438716289^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345001161 10000000000 2720438716289 6250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131616441/250000000 : ℝ)^8295 ≤ (42660393218887/100000000000000 : ℝ)^6247 := by
    have hnat : (131616441 : ℕ)^8295*100000000000000^6247 ≤ 42660393218887^6247*250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131616441 250000000 42660393218887 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251839591/10000000000 : ℝ)^8295 ≤ (6906293655693/50000000000000 : ℝ)^6247 := by
    have hnat : (2251839591 : ℕ)^8295*50000000000000^6247 ≤ 6906293655693^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251839591 10000000000 6906293655693 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345001161/10000000000 : ℝ), (131616441/250000000 : ℝ), (-2251839591/10000000000 : ℝ)] ![(2720438716289/6250000000000 : ℝ), (42660393218887/100000000000000 : ℝ), (6906293655693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345001161/10000000000 : ℝ)|^8295 ≤ (2720438716289/6250000000000 : ℝ)^6247
        have hw : |(5345001161/10000000000 : ℝ)|=(5345001161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131616441/250000000 : ℝ)|^8295 ≤ (42660393218887/100000000000000 : ℝ)^6247
        have hw : |(131616441/250000000 : ℝ)|=(131616441/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251839591/10000000000 : ℝ)|^8295 ≤ (6906293655693/50000000000000 : ℝ)^6247
        have hw : |(-2251839591/10000000000 : ℝ)|=(2251839591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370317151/10000000000 : ℝ)*x 0 + (1061089031/2500000000 : ℝ)*x 1 + (1125008567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370317151/10000000000 : ℝ)^8295 ≤ (8329130730217/25000000000000 : ℝ)^6247 := by
    have hnat : (4370317151 : ℕ)^8295*25000000000000^6247 ≤ 8329130730217^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370317151 10000000000 8329130730217 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061089031/2500000000 : ℝ)^8295 ≤ (1281901381083/4000000000000 : ℝ)^6247 := by
    have hnat : (1061089031 : ℕ)^8295*4000000000000^6247 ≤ 1281901381083^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061089031 2500000000 1281901381083 4000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125008567/2500000000 : ℝ)^8295 ≤ (34635942544587/100000000000000 : ℝ)^6247 := by
    have hnat : (1125008567 : ℕ)^8295*100000000000000^6247 ≤ 34635942544587^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125008567 2500000000 34635942544587 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370317151/10000000000 : ℝ), (1061089031/2500000000 : ℝ), (1125008567/2500000000 : ℝ)] ![(8329130730217/25000000000000 : ℝ), (1281901381083/4000000000000 : ℝ), (34635942544587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370317151/10000000000 : ℝ)|^8295 ≤ (8329130730217/25000000000000 : ℝ)^6247
        have hw : |(4370317151/10000000000 : ℝ)|=(4370317151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061089031/2500000000 : ℝ)|^8295 ≤ (1281901381083/4000000000000 : ℝ)^6247
        have hw : |(1061089031/2500000000 : ℝ)|=(1061089031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125008567/2500000000 : ℝ)|^8295 ≤ (34635942544587/100000000000000 : ℝ)^6247
        have hw : |(1125008567/2500000000 : ℝ)|=(1125008567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-546531947/2500000000 : ℝ)*x 0 + (5264984739/10000000000 : ℝ)*x 1 + (674232533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546531947/2500000000 : ℝ)^8295 ≤ (3319988090673/25000000000000 : ℝ)^6247 := by
    have hnat : (546531947 : ℕ)^8295*25000000000000^6247 ≤ 3319988090673^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546531947 2500000000 3319988090673 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264984739/10000000000 : ℝ)^8295 ≤ (10665978184329/25000000000000 : ℝ)^6247 := by
    have hnat : (5264984739 : ℕ)^8295*25000000000000^6247 ≤ 10665978184329^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264984739 10000000000 10665978184329 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674232533/1250000000 : ℝ)^8295 ≤ (44056134896391/100000000000000 : ℝ)^6247 := by
    have hnat : (674232533 : ℕ)^8295*100000000000000^6247 ≤ 44056134896391^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674232533 1250000000 44056134896391 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546531947/2500000000 : ℝ), (5264984739/10000000000 : ℝ), (674232533/1250000000 : ℝ)] ![(3319988090673/25000000000000 : ℝ), (10665978184329/25000000000000 : ℝ), (44056134896391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546531947/2500000000 : ℝ)|^8295 ≤ (3319988090673/25000000000000 : ℝ)^6247
        have hw : |(-546531947/2500000000 : ℝ)|=(546531947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264984739/10000000000 : ℝ)|^8295 ≤ (10665978184329/25000000000000 : ℝ)^6247
        have hw : |(5264984739/10000000000 : ℝ)|=(5264984739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674232533/1250000000 : ℝ)|^8295 ≤ (44056134896391/100000000000000 : ℝ)^6247
        have hw : |(674232533/1250000000 : ℝ)|=(674232533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212491317/400000000 : ℝ)*x 0 + (-2122636991/10000000000 : ℝ)*x 1 + (67423253/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212491317/400000000 : ℝ)^8295 ≤ (43173584663997/100000000000000 : ℝ)^6247 := by
    have hnat : (212491317 : ℕ)^8295*100000000000000^6247 ≤ 43173584663997^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212491317 400000000 43173584663997 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122636991/10000000000 : ℝ)^8295 ≤ (12770280683237/100000000000000 : ℝ)^6247 := by
    have hnat : (2122636991 : ℕ)^8295*100000000000000^6247 ≤ 12770280683237^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122636991 10000000000 12770280683237 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67423253/125000000 : ℝ)^8295 ≤ (44056134636097/100000000000000 : ℝ)^6247 := by
    have hnat : (67423253 : ℕ)^8295*100000000000000^6247 ≤ 44056134636097^6247*125000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67423253 125000000 44056134636097 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212491317/400000000 : ℝ), (-2122636991/10000000000 : ℝ), (67423253/125000000 : ℝ)] ![(43173584663997/100000000000000 : ℝ), (12770280683237/100000000000000 : ℝ), (44056134636097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212491317/400000000 : ℝ)|^8295 ≤ (43173584663997/100000000000000 : ℝ)^6247
        have hw : |(212491317/400000000 : ℝ)|=(212491317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122636991/10000000000 : ℝ)|^8295 ≤ (12770280683237/100000000000000 : ℝ)^6247
        have hw : |(-2122636991/10000000000 : ℝ)|=(2122636991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67423253/125000000 : ℝ)|^8295 ≤ (44056134636097/100000000000000 : ℝ)^6247
        have hw : |(67423253/125000000 : ℝ)|=(67423253/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312282927/10000000000 : ℝ)*x 0 + (2696930113/5000000000 : ℝ)*x 1 + (-132664813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312282927/10000000000 : ℝ)^8295 ≤ (2158679234279/5000000000000 : ℝ)^6247 := by
    have hnat : (5312282927 : ℕ)^8295*5000000000000^6247 ≤ 2158679234279^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312282927 10000000000 2158679234279 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696930113/5000000000 : ℝ)^8295 ≤ (2202806724213/5000000000000 : ℝ)^6247 := by
    have hnat : (2696930113 : ℕ)^8295*5000000000000^6247 ≤ 2202806724213^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696930113 5000000000 2202806724213 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132664813/625000000 : ℝ)^8295 ≤ (12770280819043/100000000000000 : ℝ)^6247 := by
    have hnat : (132664813 : ℕ)^8295*100000000000000^6247 ≤ 12770280819043^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132664813 625000000 12770280819043 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312282927/10000000000 : ℝ), (2696930113/5000000000 : ℝ), (-132664813/625000000 : ℝ)] ![(2158679234279/5000000000000 : ℝ), (2202806724213/5000000000000 : ℝ), (12770280819043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312282927/10000000000 : ℝ)|^8295 ≤ (2158679234279/5000000000000 : ℝ)^6247
        have hw : |(5312282927/10000000000 : ℝ)|=(5312282927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696930113/5000000000 : ℝ)|^8295 ≤ (2202806724213/5000000000000 : ℝ)^6247
        have hw : |(2696930113/5000000000 : ℝ)|=(2696930113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132664813/625000000 : ℝ)|^8295 ≤ (12770280819043/100000000000000 : ℝ)^6247
        have hw : |(-132664813/625000000 : ℝ)|=(132664813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s6_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370327129/10000000000 : ℝ)*x 0 + (224969429/500000000 : ℝ)*x 1 + (4245004207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370327129/10000000000 : ℝ)^8295 ≤ (16658311962049/50000000000000 : ℝ)^6247 := by
    have hnat : (4370327129 : ℕ)^8295*50000000000000^6247 ≤ 16658311962049^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370327129 10000000000 16658311962049 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224969429/500000000 : ℝ)^8295 ≤ (34629343689759/100000000000000 : ℝ)^6247 := by
    have hnat : (224969429 : ℕ)^8295*100000000000000^6247 ≤ 34629343689759^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224969429 500000000 34629343689759 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245004207/10000000000 : ℝ)^8295 ≤ (32054032369737/100000000000000 : ℝ)^6247 := by
    have hnat : (4245004207 : ℕ)^8295*100000000000000^6247 ≤ 32054032369737^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245004207 10000000000 32054032369737 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370327129/10000000000 : ℝ), (224969429/500000000 : ℝ), (4245004207/10000000000 : ℝ)] ![(16658311962049/50000000000000 : ℝ), (34629343689759/100000000000000 : ℝ), (32054032369737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370327129/10000000000 : ℝ)|^8295 ≤ (16658311962049/50000000000000 : ℝ)^6247
        have hw : |(4370327129/10000000000 : ℝ)|=(4370327129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224969429/500000000 : ℝ)|^8295 ≤ (34629343689759/100000000000000 : ℝ)^6247
        have hw : |(224969429/500000000 : ℝ)|=(224969429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245004207/10000000000 : ℝ)|^8295 ≤ (32054032369737/100000000000000 : ℝ)^6247
        have hw : |(4245004207/10000000000 : ℝ)|=(4245004207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2251/20000 : ℝ) ^ (4147/1024 : ℝ) ≤ (14392444267582557/100000000000000000000 : ℝ) := by
    have hpowers : (2251/20000 : ℝ)^4147 ≤ (14392444267582557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2251 : ℕ)^4147*100000000000000000000^1024 ≤ 14392444267582557^1024*20000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2251 20000 14392444267582557 100000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2251/20000 : ℝ)) (X := (14392444267582557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (35573976658898043/100000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^4147 ≤ (35573976658898043/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14073 : ℕ)^4147*100000000000000000000^1024 ≤ 35573976658898043^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 35573976658898043 100000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (35573976658898043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014392444267582557/50000000000000000000 : ℝ) ≤ (10000710695241049/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50014392444267582557/50000000000000000000 : ℝ)^1024 ≤ (10000710695241049/10000000000000000 : ℝ)^4147 := by
      have hnat : (50014392444267582557 : ℕ)^1024*10000000000000000^4147 ≤ 10000710695241049^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014392444267582557 50000000000000000000 10000710695241049 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000710695241049/10000000000000000 : ℝ)) (X := (50014392444267582557/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500249832104632403/500000000000000000 : ℝ) ≤ (5000616783113427/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (500249832104632403/500000000000000000 : ℝ)^1024 ≤ (5000616783113427/5000000000000000 : ℝ)^4147 := by
      have hnat : (500249832104632403 : ℕ)^1024*5000000000000000^4147 ≤ 5000616783113427^4147*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500249832104632403 500000000000000000 5000616783113427 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616783113427/5000000000000000 : ℝ)) (X := (500249832104632403/500000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035573976658898043/50000000000000000000 : ℝ) ≤ (10001756437212659/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50035573976658898043/50000000000000000000 : ℝ)^1024 ≤ (10001756437212659/10000000000000000 : ℝ)^4147 := by
      have hnat : (50035573976658898043 : ℕ)^1024*10000000000000000^4147 ≤ 10001756437212659^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035573976658898043 50000000000000000000 10001756437212659 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001756437212659/10000000000000000 : ℝ)) (X := (50035573976658898043/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14392444267582557/100000000000000000000 : ℝ) ≤ ((7042558228324701383/7045000000000000000 : ℝ)+2*(104574197161/56360000000000 : ℝ)*(2251/20000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (7042558228324701383/7045000000000000000 : ℝ)+2*(104574197161/56360000000000 : ℝ)*(2251/20000 : ℝ)=(10000710695241049/10000000000000000 : ℝ) by norm_num, show 1+2*(14392444267582557/100000000000000000000 : ℝ)=(50014392444267582557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35573976658898043/100000000000000000000 : ℝ)+(14392444267582557/100000000000000000000 : ℝ) ≤ ((7042558228324701383/7045000000000000000 : ℝ)+(104574197161/56360000000000 : ℝ)*((14073/100000 : ℝ)+(2251/20000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (7042558228324701383/7045000000000000000 : ℝ)+(104574197161/56360000000000 : ℝ)*((14073/100000 : ℝ)+(2251/20000 : ℝ))=(5000616783113427/5000000000000000 : ℝ) by norm_num, show 1+(35573976658898043/100000000000000000000 : ℝ)+(14392444267582557/100000000000000000000 : ℝ)=(500249832104632403/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35573976658898043/100000000000000000000 : ℝ) ≤ ((7042558228324701383/7045000000000000000 : ℝ)+2*(104574197161/56360000000000 : ℝ)*(14073/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (7042558228324701383/7045000000000000000 : ℝ)+2*(104574197161/56360000000000 : ℝ)*(14073/100000 : ℝ)=(10001756437212659/10000000000000000 : ℝ) by norm_num, show 1+2*(35573976658898043/100000000000000000000 : ℝ)=(50035573976658898043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7042558228324701383/7045000000000000000 : ℝ)*(X 1 0+X 2 0)+(104574197161/56360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (7042558228324701383/7045000000000000000 : ℝ)) (alpha := (104574197161/56360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7042558228324701383/7045000000000000000 : ℝ)*(X 0 1+X 2 1)+(104574197161/56360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (7042558228324701383/7045000000000000000 : ℝ)) (alpha := (104574197161/56360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7042558228324701383/7045000000000000000 : ℝ)*(X 0 2+X 1 2)+(104574197161/56360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (7042558228324701383/7045000000000000000 : ℝ)) (alpha := (104574197161/56360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093061343/5000000000 : ℝ)*X 0 0+(215767541/400000000 : ℝ)*X 0 1+(2632328841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668125141/1250000000 : ℝ)*X 1 0+(-2251839633/10000000000 : ℝ)*X 1 1+(5264657641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345001161/10000000000 : ℝ)*X 2 0+(131616441/250000000 : ℝ)*X 2 1+(-2251839591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370317151/10000000000 : ℝ)*X 0 0+(1061089031/2500000000 : ℝ)*X 0 1+(1125008567/2500000000 : ℝ)*X 0 2+(4370317151/10000000000 : ℝ)*X 1 0+(1061089031/2500000000 : ℝ)*X 1 1+(1125008567/2500000000 : ℝ)*X 1 2+(4370317151/10000000000 : ℝ)*X 2 0+(1061089031/2500000000 : ℝ)*X 2 1+(1125008567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546531947/2500000000 : ℝ)*X 0 0+(5264984739/10000000000 : ℝ)*X 0 1+(674232533/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212491317/400000000 : ℝ)*X 1 0+(-2122636991/10000000000 : ℝ)*X 1 1+(67423253/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312282927/10000000000 : ℝ)*X 2 0+(2696930113/5000000000 : ℝ)*X 2 1+(-132664813/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370327129/10000000000 : ℝ)*X 0 0+(224969429/500000000 : ℝ)*X 0 1+(4245004207/10000000000 : ℝ)*X 0 2+(4370327129/10000000000 : ℝ)*X 1 0+(224969429/500000000 : ℝ)*X 1 1+(4245004207/10000000000 : ℝ)*X 1 2+(4370327129/10000000000 : ℝ)*X 2 0+(224969429/500000000 : ℝ)*X 2 1+(4245004207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (284274413535167518691426727/35225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (438195217/25000000000000 : ℝ)*(base19) + (834272659/50000000000000 : ℝ)*(base23) + (70500767/100000000000000 : ℝ)*(lower2) + (193483899/100000000000000 : ℝ)*(upper3) + (42764767/25000000000000 : ℝ)*(upper5) + (1163147782238777/20000000000000 : ℝ)*(major0) + (1163147782238777/20000000000000 : ℝ)*(major1) + (1163147782238777/20000000000000 : ℝ)*(major2) + (241256693150207/3125000000000 : ℝ)*(sp0) + (1930064810812361/25000000000000 : ℝ)*(sp1) + (1544051865496999/20000000000000 : ℝ)*(sp2) + (1955595585152799/50000000000000 : ℝ)*(sp3) + (5851902961/12500000000000 : ℝ)*(sp4) + (3173380457/12500000000000 : ℝ)*(sp7) + (1955608278674627/50000000000000 : ℝ)*(f.failure) + (965032624503789/12500000000000 : ℝ)*(f.sum) + (8401927771567/2818000000000000000000000000 : ℝ)*base66 + (666415919882653591/140900000000000000000000000000000 : ℝ)*base67 + (1199187761869853591/140900000000000000000000000000000 : ℝ)*base69 + (675192568201653591/140900000000000000000000000000000 : ℝ)*base71 + (3027094152391/563600000000000000000000000 : ℝ)*base74 + (1907767478853746409/140900000000000000000000000000000 : ℝ)*base76 + (263805941654953591/140900000000000000000000000000000 : ℝ)*base77 + (61106030071453591/140900000000000000000000000000000 : ℝ)*base79 + (13159392521487/2818000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1364847/5000000000000000000000 : ℝ)*base89 + (1364847/5000000000000000000000 : ℝ)*base91 + (1364847/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1246173964998314926054270677/176125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1558587543/100000000000000 : ℝ)*(base19) + (40175983/2500000000000 : ℝ)*(base23) + (72471411/50000000000000 : ℝ)*(upper3) + (26860633/100000000000000 : ℝ)*(lower4) + (87973887/50000000000000 : ℝ)*(upper5) + (5845242163350227/100000000000000 : ℝ)*(major0) + (5845242163350227/100000000000000 : ℝ)*(major1) + (5845242163350227/100000000000000 : ℝ)*(major2) + (21452422987/50000000000000 : ℝ)*(sp1) + (5260957181/12500000000000 : ℝ)*(sp2) + (7759425926081519/100000000000000 : ℝ)*(sp4) + (7759381462648001/100000000000000 : ℝ)*(sp5) + (7759382231384751/100000000000000 : ℝ)*(sp6) + (982764541192159/25000000000000 : ℝ)*(sp7) + (982764541192159/25000000000000 : ℝ)*(f.failure) + (7759425926081519/100000000000000 : ℝ)*(f.sum) + (3064380465349/2818000000000000000000000000 : ℝ)*base66 + (12540168585719138941/704500000000000000000000000000000 : ℝ)*base67 + (1751950524792361059/704500000000000000000000000000000 : ℝ)*base70 + (1797845346729138941/704500000000000000000000000000000 : ℝ)*base71 + (20344661584299/2818000000000000000000000000 : ℝ)*base74 + (2406215205096638941/704500000000000000000000000000000 : ℝ)*base75 + (1134346043443138941/704500000000000000000000000000000 : ℝ)*base77 + (18857435651646638941/704500000000000000000000000000000 : ℝ)*base79 + (15209359679021/2818000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10364101/2500000000000000000000 : ℝ)*base90 + (10364101/2500000000000000000000 : ℝ)*base92 + (10364101/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1102_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s7_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093078757/5000000000 : ℝ)*x 0 + (5393797997/10000000000 : ℝ)*x 1 + (82266019/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093078757/5000000000 : ℝ)^8295 ≤ (166002401717/1250000000000 : ℝ)^6247 := by
    have hnat : (1093078757 : ℕ)^8295*1250000000000^6247 ≤ 166002401717^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093078757 5000000000 166002401717 1250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393797997/10000000000 : ℝ)^8295 ≤ (22027729788899/50000000000000 : ℝ)^6247 := by
    have hnat : (5393797997 : ℕ)^8295*50000000000000^6247 ≤ 22027729788899^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393797997 10000000000 22027729788899 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82266019/156250000 : ℝ)^8295 ≤ (42664348266553/100000000000000 : ℝ)^6247 := by
    have hnat : (82266019 : ℕ)^8295*100000000000000^6247 ≤ 42664348266553^6247*156250000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82266019 156250000 42664348266553 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093078757/5000000000 : ℝ), (5393797997/10000000000 : ℝ), (82266019/156250000 : ℝ)] ![(166002401717/1250000000000 : ℝ), (22027729788899/50000000000000 : ℝ), (42664348266553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093078757/5000000000 : ℝ)|^8295 ≤ (166002401717/1250000000000 : ℝ)^6247
        have hw : |(-1093078757/5000000000 : ℝ)|=(1093078757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393797997/10000000000 : ℝ)|^8295 ≤ (22027729788899/50000000000000 : ℝ)^6247
        have hw : |(5393797997/10000000000 : ℝ)|=(5393797997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82266019/156250000 : ℝ)|^8295 ≤ (42664348266553/100000000000000 : ℝ)^6247
        have hw : |(82266019/156250000 : ℝ)|=(82266019/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53449029/100000000 : ℝ)*x 0 + (-140717769/625000000 : ℝ)*x 1 + (5265025323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53449029/100000000 : ℝ)^8295 ≤ (43525956943639/100000000000000 : ℝ)^6247 := by
    have hnat : (53449029 : ℕ)^8295*100000000000000^6247 ≤ 43525956943639^6247*100000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53449029 100000000 43525956943639 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140717769/625000000 : ℝ)^8295 ≤ (43155292597/312500000000 : ℝ)^6247 := by
    have hnat : (140717769 : ℕ)^8295*312500000000^6247 ≤ 43155292597^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140717769 625000000 43155292597 312500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265025323/10000000000 : ℝ)^8295 ≤ (21332174708933/50000000000000 : ℝ)^6247 := by
    have hnat : (5265025323 : ℕ)^8295*50000000000000^6247 ≤ 21332174708933^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265025323 10000000000 21332174708933 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53449029/100000000 : ℝ), (-140717769/625000000 : ℝ), (5265025323/10000000000 : ℝ)] ![(43525956943639/100000000000000 : ℝ), (43155292597/312500000000 : ℝ), (21332174708933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53449029/100000000 : ℝ)|^8295 ≤ (43525956943639/100000000000000 : ℝ)^6247
        have hw : |(53449029/100000000 : ℝ)|=(53449029/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140717769/625000000 : ℝ)|^8295 ≤ (43155292597/312500000000 : ℝ)^6247
        have hw : |(-140717769/625000000 : ℝ)|=(140717769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265025323/10000000000 : ℝ)|^8295 ≤ (21332174708933/50000000000000 : ℝ)^6247
        have hw : |(5265025323/10000000000 : ℝ)|=(5265025323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068980633/2000000000 : ℝ)*x 0 + (658128143/1250000000 : ℝ)*x 1 + (-2251484189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068980633/2000000000 : ℝ)^8295 ≤ (10881489952283/25000000000000 : ℝ)^6247 := by
    have hnat : (1068980633 : ℕ)^8295*25000000000000^6247 ≤ 10881489952283^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068980633 2000000000 10881489952283 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658128143/1250000000 : ℝ)^8295 ≤ (21332173745919/50000000000000 : ℝ)^6247 := by
    have hnat : (658128143 : ℕ)^8295*50000000000000^6247 ≤ 21332173745919^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658128143 1250000000 21332173745919 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251484189/10000000000 : ℝ)^8295 ≤ (431552896701/3125000000000 : ℝ)^6247 := by
    have hnat : (2251484189 : ℕ)^8295*3125000000000^6247 ≤ 431552896701^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251484189 10000000000 431552896701 3125000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068980633/2000000000 : ℝ), (658128143/1250000000 : ℝ), (-2251484189/10000000000 : ℝ)] ![(10881489952283/25000000000000 : ℝ), (21332173745919/50000000000000 : ℝ), (431552896701/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068980633/2000000000 : ℝ)|^8295 ≤ (10881489952283/25000000000000 : ℝ)^6247
        have hw : |(1068980633/2000000000 : ℝ)|=(1068980633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658128143/1250000000 : ℝ)|^8295 ≤ (21332173745919/50000000000000 : ℝ)^6247
        have hw : |(658128143/1250000000 : ℝ)|=(658128143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251484189/10000000000 : ℝ)|^8295 ≤ (431552896701/3125000000000 : ℝ)^6247
        have hw : |(-2251484189/10000000000 : ℝ)|=(2251484189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370336549/10000000000 : ℝ)*x 0 + (1061275507/2500000000 : ℝ)*x 1 + (1124820819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370336549/10000000000 : ℝ)^8295 ≤ (33316719278991/100000000000000 : ℝ)^6247 := by
    have hnat : (4370336549 : ℕ)^8295*100000000000000^6247 ≤ 33316719278991^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370336549 10000000000 33316719278991 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061275507/2500000000 : ℝ)^8295 ≤ (16027506587931/50000000000000 : ℝ)^6247 := by
    have hnat : (1061275507 : ℕ)^8295*50000000000000^6247 ≤ 16027506587931^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061275507 2500000000 16027506587931 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124820819/2500000000 : ℝ)^8295 ≤ (34628267524803/100000000000000 : ℝ)^6247 := by
    have hnat : (1124820819 : ℕ)^8295*100000000000000^6247 ≤ 34628267524803^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124820819 2500000000 34628267524803 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370336549/10000000000 : ℝ), (1061275507/2500000000 : ℝ), (1124820819/2500000000 : ℝ)] ![(33316719278991/100000000000000 : ℝ), (16027506587931/50000000000000 : ℝ), (34628267524803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370336549/10000000000 : ℝ)|^8295 ≤ (33316719278991/100000000000000 : ℝ)^6247
        have hw : |(4370336549/10000000000 : ℝ)|=(4370336549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061275507/2500000000 : ℝ)|^8295 ≤ (16027506587931/50000000000000 : ℝ)^6247
        have hw : |(1061275507/2500000000 : ℝ)|=(1061275507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124820819/2500000000 : ℝ)|^8295 ≤ (34628267524803/100000000000000 : ℝ)^6247
        have hw : |(1124820819/2500000000 : ℝ)|=(1124820819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273270331/1250000000 : ℝ)*x 0 + (1316337141/2500000000 : ℝ)*x 1 + (168546043/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273270331/1250000000 : ℝ)^8295 ≤ (13280233549133/100000000000000 : ℝ)^6247 := by
    have hnat : (273270331 : ℕ)^8295*100000000000000^6247 ≤ 13280233549133^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273270331 1250000000 13280233549133 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316337141/2500000000 : ℝ)^8295 ≤ (21333913752107/50000000000000 : ℝ)^6247 := by
    have hnat : (1316337141 : ℕ)^8295*50000000000000^6247 ≤ 21333913752107^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316337141 2500000000 21333913752107 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168546043/312500000 : ℝ)^8295 ≤ (11012984733131/25000000000000 : ℝ)^6247 := by
    have hnat : (168546043 : ℕ)^8295*25000000000000^6247 ≤ 11012984733131^6247*312500000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168546043 312500000 11012984733131 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273270331/1250000000 : ℝ), (1316337141/2500000000 : ℝ), (168546043/312500000 : ℝ)] ![(13280233549133/100000000000000 : ℝ), (21333913752107/50000000000000 : ℝ), (11012984733131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273270331/1250000000 : ℝ)|^8295 ≤ (13280233549133/100000000000000 : ℝ)^6247
        have hw : |(-273270331/1250000000 : ℝ)|=(273270331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316337141/2500000000 : ℝ)|^8295 ≤ (21333913752107/50000000000000 : ℝ)^6247
        have hw : |(1316337141/2500000000 : ℝ)|=(1316337141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168546043/312500000 : ℝ)|^8295 ≤ (11012984733131/25000000000000 : ℝ)^6247
        have hw : |(168546043/312500000 : ℝ)|=(168546043/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328094039/2500000000 : ℝ)*x 0 + (-2123036153/10000000000 : ℝ)*x 1 + (5393473447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328094039/2500000000 : ℝ)^8295 ≤ (21587295384593/50000000000000 : ℝ)^6247 := by
    have hnat : (1328094039 : ℕ)^8295*50000000000000^6247 ≤ 21587295384593^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328094039 2500000000 21587295384593 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123036153/10000000000 : ℝ)^8295 ≤ (12773469519171/100000000000000 : ℝ)^6247 := by
    have hnat : (2123036153 : ℕ)^8295*100000000000000^6247 ≤ 12773469519171^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123036153 10000000000 12773469519171 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393473447/10000000000 : ℝ)^8295 ≤ (2202596985127/5000000000000 : ℝ)^6247 := by
    have hnat : (5393473447 : ℕ)^8295*5000000000000^6247 ≤ 2202596985127^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393473447 10000000000 2202596985127 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328094039/2500000000 : ℝ), (-2123036153/10000000000 : ℝ), (5393473447/10000000000 : ℝ)] ![(21587295384593/50000000000000 : ℝ), (12773469519171/100000000000000 : ℝ), (2202596985127/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328094039/2500000000 : ℝ)|^8295 ≤ (21587295384593/50000000000000 : ℝ)^6247
        have hw : |(1328094039/2500000000 : ℝ)|=(1328094039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123036153/10000000000 : ℝ)|^8295 ≤ (12773469519171/100000000000000 : ℝ)^6247
        have hw : |(-2123036153/10000000000 : ℝ)|=(2123036153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393473447/10000000000 : ℝ)|^8295 ≤ (2202596985127/5000000000000 : ℝ)^6247
        have hw : |(5393473447/10000000000 : ℝ)|=(5393473447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212495047/400000000 : ℝ)*x 0 + (5393473411/10000000000 : ℝ)*x 1 + (-132689761/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212495047/400000000 : ℝ)^8295 ≤ (1726983638969/4000000000000 : ℝ)^6247 := by
    have hnat : (212495047 : ℕ)^8295*4000000000000^6247 ≤ 1726983638969^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212495047 400000000 1726983638969 4000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393473411/10000000000 : ℝ)^8295 ≤ (44051939312109/100000000000000 : ℝ)^6247 := by
    have hnat : (5393473411 : ℕ)^8295*100000000000000^6247 ≤ 44051939312109^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393473411 10000000000 44051939312109 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132689761/625000000 : ℝ)^8295 ≤ (319336742573/2500000000000 : ℝ)^6247 := by
    have hnat : (132689761 : ℕ)^8295*2500000000000^6247 ≤ 319336742573^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132689761 625000000 319336742573 2500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212495047/400000000 : ℝ), (5393473411/10000000000 : ℝ), (-132689761/625000000 : ℝ)] ![(1726983638969/4000000000000 : ℝ), (44051939312109/100000000000000 : ℝ), (319336742573/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212495047/400000000 : ℝ)|^8295 ≤ (1726983638969/4000000000000 : ℝ)^6247
        have hw : |(212495047/400000000 : ℝ)|=(212495047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393473411/10000000000 : ℝ)|^8295 ≤ (44051939312109/100000000000000 : ℝ)^6247
        have hw : |(5393473411/10000000000 : ℝ)|=(5393473411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132689761/625000000 : ℝ)|^8295 ≤ (319336742573/2500000000000 : ℝ)^6247
        have hw : |(-132689761/625000000 : ℝ)|=(132689761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s7_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370346311/10000000000 : ℝ)*x 0 + (4498645243/10000000000 : ℝ)*x 1 + (849148491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370346311/10000000000 : ℝ)^8295 ≤ (8329204523971/25000000000000 : ℝ)^6247 := by
    have hnat : (4370346311 : ℕ)^8295*25000000000000^6247 ≤ 8329204523971^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370346311 10000000000 8329204523971 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498645243/10000000000 : ℝ)^8295 ≤ (34621747258147/100000000000000 : ℝ)^6247 := by
    have hnat : (4498645243 : ℕ)^8295*100000000000000^6247 ≤ 34621747258147^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498645243 10000000000 34621747258147 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849148491/2000000000 : ℝ)^8295 ≤ (16030717312773/50000000000000 : ℝ)^6247 := by
    have hnat : (849148491 : ℕ)^8295*50000000000000^6247 ≤ 16030717312773^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849148491 2000000000 16030717312773 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370346311/10000000000 : ℝ), (4498645243/10000000000 : ℝ), (849148491/2000000000 : ℝ)] ![(8329204523971/25000000000000 : ℝ), (34621747258147/100000000000000 : ℝ), (16030717312773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370346311/10000000000 : ℝ)|^8295 ≤ (8329204523971/25000000000000 : ℝ)^6247
        have hw : |(4370346311/10000000000 : ℝ)|=(4370346311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498645243/10000000000 : ℝ)|^8295 ≤ (34621747258147/100000000000000 : ℝ)^6247
        have hw : |(4498645243/10000000000 : ℝ)|=(4498645243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849148491/2000000000 : ℝ)|^8295 ≤ (16030717312773/50000000000000 : ℝ)^6247
        have hw : |(849148491/2000000000 : ℝ)|=(849148491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11291/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (1457978981596673/10000000000000000000 : ℝ) := by
    have hpowers : (11291/100000 : ℝ)^4147 ≤ (1457978981596673/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11291 : ℕ)^4147*10000000000000000000^1024 ≤ 1457978981596673^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11291 100000 1457978981596673 10000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11291/100000 : ℝ)) (X := (1457978981596673/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/20000 : ℝ) ^ (4147/1024 : ℝ) ≤ (4398320390125587/12500000000000000000 : ℝ) := by
    have hpowers : (2807/20000 : ℝ)^4147 ≤ (4398320390125587/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2807 : ℕ)^4147*12500000000000000000^1024 ≤ 4398320390125587^1024*20000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 20000 4398320390125587 12500000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/20000 : ℝ)) (X := (4398320390125587/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001457978981596673/5000000000000000000 : ℝ) ≤ (10000719945301123/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (5001457978981596673/5000000000000000000 : ℝ)^1024 ≤ (10000719945301123/10000000000000000 : ℝ)^4147 := by
      have hnat : (5001457978981596673 : ℕ)^1024*10000000000000000^4147 ≤ 10000719945301123^4147*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001457978981596673 5000000000000000000 10000719945301123 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000719945301123/10000000000000000 : ℝ)) (X := (5001457978981596673/5000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024883176468485713/50000000000000000000 : ℝ) ≤ (10001228627892637/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50024883176468485713/50000000000000000000 : ℝ)^1024 ≤ (10001228627892637/10000000000000000 : ℝ)^4147 := by
      have hnat : (50024883176468485713 : ℕ)^1024*10000000000000000^4147 ≤ 10001228627892637^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024883176468485713 50000000000000000000 10001228627892637 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228627892637/10000000000000000 : ℝ)) (X := (50024883176468485713/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254398320390125587/6250000000000000000 : ℝ) ≤ (10001737310484151/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (6254398320390125587/6250000000000000000 : ℝ)^1024 ≤ (10001737310484151/10000000000000000 : ℝ)^4147 := by
      have hnat : (6254398320390125587 : ℕ)^1024*10000000000000000^4147 ≤ 10001737310484151^4147*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254398320390125587 6250000000000000000 10001737310484151 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001737310484151/10000000000000000 : ℝ)) (X := (6254398320390125587/6250000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1457978981596673/10000000000000000000 : ℝ) ≤ ((979660302129454013/980000000000000000 : ℝ)+2*(254341295757/137200000000000 : ℝ)*(11291/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (979660302129454013/980000000000000000 : ℝ)+2*(254341295757/137200000000000 : ℝ)*(11291/100000 : ℝ)=(10000719945301123/10000000000000000 : ℝ) by norm_num, show 1+2*(1457978981596673/10000000000000000000 : ℝ)=(5001457978981596673/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4398320390125587/12500000000000000000 : ℝ)+(1457978981596673/10000000000000000000 : ℝ) ≤ ((979660302129454013/980000000000000000 : ℝ)+(254341295757/137200000000000 : ℝ)*((2807/20000 : ℝ)+(11291/100000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (979660302129454013/980000000000000000 : ℝ)+(254341295757/137200000000000 : ℝ)*((2807/20000 : ℝ)+(11291/100000 : ℝ))=(10001228627892637/10000000000000000 : ℝ) by norm_num, show 1+(4398320390125587/12500000000000000000 : ℝ)+(1457978981596673/10000000000000000000 : ℝ)=(50024883176468485713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4398320390125587/12500000000000000000 : ℝ) ≤ ((979660302129454013/980000000000000000 : ℝ)+2*(254341295757/137200000000000 : ℝ)*(2807/20000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (979660302129454013/980000000000000000 : ℝ)+2*(254341295757/137200000000000 : ℝ)*(2807/20000 : ℝ)=(10001737310484151/10000000000000000 : ℝ) by norm_num, show 1+2*(4398320390125587/12500000000000000000 : ℝ)=(6254398320390125587/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (979660302129454013/980000000000000000 : ℝ)*(X 1 0+X 2 0)+(254341295757/137200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (979660302129454013/980000000000000000 : ℝ)) (alpha := (254341295757/137200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (979660302129454013/980000000000000000 : ℝ)*(X 0 1+X 2 1)+(254341295757/137200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (979660302129454013/980000000000000000 : ℝ)) (alpha := (254341295757/137200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (979660302129454013/980000000000000000 : ℝ)*(X 0 2+X 1 2)+(254341295757/137200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (979660302129454013/980000000000000000 : ℝ)) (alpha := (254341295757/137200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093078757/5000000000 : ℝ)*X 0 0+(5393797997/10000000000 : ℝ)*X 0 1+(82266019/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53449029/100000000 : ℝ)*X 1 0+(-140717769/625000000 : ℝ)*X 1 1+(5265025323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068980633/2000000000 : ℝ)*X 2 0+(658128143/1250000000 : ℝ)*X 2 1+(-2251484189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370336549/10000000000 : ℝ)*X 0 0+(1061275507/2500000000 : ℝ)*X 0 1+(1124820819/2500000000 : ℝ)*X 0 2+(4370336549/10000000000 : ℝ)*X 1 0+(1061275507/2500000000 : ℝ)*X 1 1+(1124820819/2500000000 : ℝ)*X 1 2+(4370336549/10000000000 : ℝ)*X 2 0+(1061275507/2500000000 : ℝ)*X 2 1+(1124820819/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273270331/1250000000 : ℝ)*X 0 0+(1316337141/2500000000 : ℝ)*X 0 1+(168546043/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328094039/2500000000 : ℝ)*X 1 0+(-2123036153/10000000000 : ℝ)*X 1 1+(5393473447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212495047/400000000 : ℝ)*X 2 0+(5393473411/10000000000 : ℝ)*X 2 1+(-132689761/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370346311/10000000000 : ℝ)*X 0 0+(4498645243/10000000000 : ℝ)*X 0 1+(849148491/2000000000 : ℝ)*X 0 2+(4370346311/10000000000 : ℝ)*X 1 0+(4498645243/10000000000 : ℝ)*X 1 1+(849148491/2000000000 : ℝ)*X 1 2+(4370346311/10000000000 : ℝ)*X 2 0+(4498645243/10000000000 : ℝ)*X 2 1+(849148491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138430707631699706422329351/21437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1406115763/100000000000000 : ℝ)*(base19) + (737166841/50000000000000 : ℝ)*(base23) + (16932941/10000000000000 : ℝ)*(lower2) + (47149811/50000000000000 : ℝ)*(upper3) + (57083291/50000000000000 : ℝ)*(upper5) + (365623409319571/6250000000000 : ℝ)*(major0) + (365623409319571/6250000000000 : ℝ)*(major1) + (365623409319571/6250000000000 : ℝ)*(major2) + (776565712017947/10000000000000 : ℝ)*(sp0) + (1941426668786167/25000000000000 : ℝ)*(sp1) + (7765706606926749/100000000000000 : ℝ)*(sp2) + (1967109470825279/50000000000000 : ℝ)*(sp3) + (50961080961/100000000000000 : ℝ)*(sp4) + (5465017077/25000000000000 : ℝ)*(sp7) + (1967120400859433/50000000000000 : ℝ)*(f.failure) + (7765708081260431/100000000000000 : ℝ)*(f.sum) + (2048558918129/857500000000000000000000000 : ℝ)*base65 + (101201344061818961/42875000000000000000000000000000 : ℝ)*base67 + (198459339548568961/42875000000000000000000000000000 : ℝ)*base69 + (1723143446318961/42875000000000000000000000000000 : ℝ)*base71 + (157976751447/107187500000000000000000000 : ℝ)*base74 + (439463234243068961/42875000000000000000000000000000 : ℝ)*base75 + (98598203314443961/42875000000000000000000000000000 : ℝ)*base77 + (675916483453568961/42875000000000000000000000000000 : ℝ)*base79 + (13378459854283/1715000000000000000000000000 : ℝ)*base81 + (11040813/5000000000000000000000 : ℝ)*base89 + (11040813/5000000000000000000000 : ℝ)*base91 + (11040813/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64828002770960193194515569/7000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352397847/20000000000000 : ℝ)*(base19) + (94480287/5000000000000 : ℝ)*(base23) + (22157287/10000000000000 : ℝ)*(upper3) + (8667147/20000000000000 : ℝ)*(lower4) + (43438821/25000000000000 : ℝ)*(upper5) + (5879487938259103/100000000000000 : ℝ)*(major0) + (5879487938259103/100000000000000 : ℝ)*(major1) + (5879487938259103/100000000000000 : ℝ)*(major2) + (50254283499/100000000000000 : ℝ)*(sp1) + (2660721051/5000000000000 : ℝ)*(sp2) + (780488634131933/10000000000000 : ℝ)*(sp4) + (1951208581261649/25000000000000 : ℝ)*(sp5) + (7804831237292571/100000000000000 : ℝ)*(sp6) + (1977044613247047/50000000000000 : ℝ)*(sp7) + (1977044613247047/50000000000000 : ℝ)*(f.failure) + (780488634131933/10000000000000 : ℝ)*(f.sum) + (2383968994733/980000000000000000000000000 : ℝ)*base65 + (195510138883780339/98000000000000000000000000000000 : ℝ)*base67 + (538468886140219661/98000000000000000000000000000000 : ℝ)*base70 + (1370906228779780339/98000000000000000000000000000000 : ℝ)*base71 + (721267397987/980000000000000000000000000 : ℝ)*base74 + (544370009977780339/98000000000000000000000000000000 : ℝ)*base75 + (614462638177780339/98000000000000000000000000000000 : ℝ)*base77 + (1660366276334219661/98000000000000000000000000000000 : ℝ)*base80 + (2481199943267/980000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15278467/5000000000000000000000 : ℝ)*base89 + (15278467/5000000000000000000000 : ℝ)*base91 + (15278467/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1102_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1102_s8_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-218616361/1000000000 : ℝ)*x 0 + (269685759/500000000 : ℝ)*x 1 + (2632552061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218616361/1000000000 : ℝ)^8295 ≤ (6640120654401/50000000000000 : ℝ)^6247 := by
    have hnat : (218616361 : ℕ)^8295*50000000000000^6247 ≤ 6640120654401^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218616361 1000000000 6640120654401 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269685759/500000000 : ℝ)^8295 ≤ (11013640346883/25000000000000 : ℝ)^6247 := by
    have hnat : (269685759 : ℕ)^8295*25000000000000^6247 ≤ 11013640346883^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269685759 500000000 11013640346883 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632552061/5000000000 : ℝ)^8295 ≤ (10666299322967/25000000000000 : ℝ)^6247 := by
    have hnat : (2632552061 : ℕ)^8295*25000000000000^6247 ≤ 10666299322967^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632552061 5000000000 10666299322967 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218616361/1000000000 : ℝ), (269685759/500000000 : ℝ), (2632552061/5000000000 : ℝ)] ![(6640120654401/50000000000000 : ℝ), (11013640346883/25000000000000 : ℝ), (10666299322967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218616361/1000000000 : ℝ)|^8295 ≤ (6640120654401/50000000000000 : ℝ)^6247
        have hw : |(-218616361/1000000000 : ℝ)|=(218616361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269685759/500000000 : ℝ)|^8295 ≤ (11013640346883/25000000000000 : ℝ)^6247
        have hw : |(269685759/500000000 : ℝ)|=(269685759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632552061/5000000000 : ℝ)|^8295 ≤ (10666299322967/25000000000000 : ℝ)^6247
        have hw : |(2632552061/5000000000 : ℝ)|=(2632552061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336220641/2500000000 : ℝ)*x 0 + (-2251407253/10000000000 : ℝ)*x 1 + (65813801/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336220641/2500000000 : ℝ)^8295 ≤ (5440717130871/12500000000000 : ℝ)^6247 := by
    have hnat : (1336220641 : ℕ)^8295*12500000000000^6247 ≤ 5440717130871^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336220641 2500000000 5440717130871 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251407253/10000000000 : ℝ)^8295 ≤ (6904533049541/50000000000000 : ℝ)^6247 := by
    have hnat : (2251407253 : ℕ)^8295*50000000000000^6247 ≤ 6904533049541^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251407253 10000000000 6904533049541 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65813801/125000000 : ℝ)^8295 ≤ (42665196839949/100000000000000 : ℝ)^6247 := by
    have hnat : (65813801 : ℕ)^8295*100000000000000^6247 ≤ 42665196839949^6247*125000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65813801 125000000 42665196839949 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336220641/2500000000 : ℝ), (-2251407253/10000000000 : ℝ), (65813801/125000000 : ℝ)] ![(5440717130871/12500000000000 : ℝ), (6904533049541/50000000000000 : ℝ), (42665196839949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336220641/2500000000 : ℝ)|^8295 ≤ (5440717130871/12500000000000 : ℝ)^6247
        have hw : |(1336220641/2500000000 : ℝ)|=(1336220641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251407253/10000000000 : ℝ)|^8295 ≤ (6904533049541/50000000000000 : ℝ)^6247
        have hw : |(-2251407253/10000000000 : ℝ)|=(2251407253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65813801/125000000 : ℝ)|^8295 ≤ (42665196839949/100000000000000 : ℝ)^6247
        have hw : |(65813801/125000000 : ℝ)|=(65813801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668110321/1250000000 : ℝ)*x 0 + (5265104111/10000000000 : ℝ)*x 1 + (-2251407207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668110321/1250000000 : ℝ)^8295 ≤ (43525737090221/100000000000000 : ℝ)^6247 := by
    have hnat : (668110321 : ℕ)^8295*100000000000000^6247 ≤ 43525737090221^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668110321 1250000000 43525737090221 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265104111/10000000000 : ℝ)^8295 ≤ (42665197173509/100000000000000 : ℝ)^6247 := by
    have hnat : (5265104111 : ℕ)^8295*100000000000000^6247 ≤ 42665197173509^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265104111 10000000000 42665197173509 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251407207/10000000000 : ℝ)^8295 ≤ (13809065724443/100000000000000 : ℝ)^6247 := by
    have hnat : (2251407207 : ℕ)^8295*100000000000000^6247 ≤ 13809065724443^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251407207 10000000000 13809065724443 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668110321/1250000000 : ℝ), (5265104111/10000000000 : ℝ), (-2251407207/10000000000 : ℝ)] ![(43525737090221/100000000000000 : ℝ), (42665197173509/100000000000000 : ℝ), (13809065724443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668110321/1250000000 : ℝ)|^8295 ≤ (43525737090221/100000000000000 : ℝ)^6247
        have hw : |(668110321/1250000000 : ℝ)|=(668110321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265104111/10000000000 : ℝ)|^8295 ≤ (42665197173509/100000000000000 : ℝ)^6247
        have hw : |(5265104111/10000000000 : ℝ)|=(5265104111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251407207/10000000000 : ℝ)|^8295 ≤ (13809065724443/100000000000000 : ℝ)^6247
        have hw : |(-2251407207/10000000000 : ℝ)|=(2251407207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185170257/5000000000 : ℝ)*x 0 + (2122630463/5000000000 : ℝ)*x 1 + (89982469/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185170257/5000000000 : ℝ)^8295 ≤ (416459492689/1250000000000 : ℝ)^6247 := by
    have hnat : (2185170257 : ℕ)^8295*1250000000000^6247 ≤ 416459492689^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185170257 5000000000 416459492689 1250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122630463/5000000000 : ℝ)^8295 ≤ (62610559353/195312500000 : ℝ)^6247 := by
    have hnat : (2122630463 : ℕ)^8295*195312500000^6247 ≤ 62610559353^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122630463 5000000000 62610559353 195312500000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89982469/200000000 : ℝ)^8295 ≤ (34626634182491/100000000000000 : ℝ)^6247 := by
    have hnat : (89982469 : ℕ)^8295*100000000000000^6247 ≤ 34626634182491^6247*200000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89982469 200000000 34626634182491 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185170257/5000000000 : ℝ), (2122630463/5000000000 : ℝ), (89982469/200000000 : ℝ)] ![(416459492689/1250000000000 : ℝ), (62610559353/195312500000 : ℝ), (34626634182491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185170257/5000000000 : ℝ)|^8295 ≤ (416459492689/1250000000000 : ℝ)^6247
        have hw : |(2185170257/5000000000 : ℝ)|=(2185170257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122630463/5000000000 : ℝ)|^8295 ≤ (62610559353/195312500000 : ℝ)^6247
        have hw : |(2122630463/5000000000 : ℝ)|=(2122630463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89982469/200000000 : ℝ)|^8295 ≤ (34626634182491/100000000000000 : ℝ)^6247
        have hw : |(89982469/200000000 : ℝ)|=(89982469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273271077/1250000000 : ℝ)*x 0 + (5265426603/10000000000 : ℝ)*x 1 + (539339151/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273271077/1250000000 : ℝ)^8295 ≤ (13280281688141/100000000000000 : ℝ)^6247 := by
    have hnat : (273271077 : ℕ)^8295*100000000000000^6247 ≤ 13280281688141^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273271077 1250000000 13280281688141 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265426603/10000000000 : ℝ)^8295 ≤ (5333583402191/12500000000000 : ℝ)^6247 := by
    have hnat : (5265426603 : ℕ)^8295*12500000000000^6247 ≤ 5333583402191^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265426603 10000000000 5333583402191 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539339151/1000000000 : ℝ)^8295 ≤ (11012762768451/25000000000000 : ℝ)^6247 := by
    have hnat : (539339151 : ℕ)^8295*25000000000000^6247 ≤ 11012762768451^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539339151 1000000000 11012762768451 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273271077/1250000000 : ℝ), (5265426603/10000000000 : ℝ), (539339151/1000000000 : ℝ)] ![(13280281688141/100000000000000 : ℝ), (5333583402191/12500000000000 : ℝ), (11012762768451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273271077/1250000000 : ℝ)|^8295 ≤ (13280281688141/100000000000000 : ℝ)^6247
        have hw : |(-273271077/1250000000 : ℝ)|=(273271077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265426603/10000000000 : ℝ)|^8295 ≤ (5333583402191/12500000000000 : ℝ)^6247
        have hw : |(5265426603/10000000000 : ℝ)|=(5265426603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539339151/1000000000 : ℝ)|^8295 ≤ (11012762768451/25000000000000 : ℝ)^6247
        have hw : |(539339151/1000000000 : ℝ)|=(539339151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66404957/125000000 : ℝ)*x 0 + (-84924793/400000000 : ℝ)*x 1 + (5393391507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66404957/125000000 : ℝ)^8295 ≤ (10793702740087/25000000000000 : ℝ)^6247 := by
    have hnat : (66404957 : ℕ)^8295*25000000000000^6247 ≤ 10793702740087^6247*125000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66404957 125000000 10793702740087 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84924793/400000000 : ℝ)^8295 ≤ (1596767248147/12500000000000 : ℝ)^6247 := by
    have hnat : (84924793 : ℕ)^8295*12500000000000^6247 ≤ 1596767248147^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84924793 400000000 1596767248147 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393391507/10000000000 : ℝ)^8295 ≤ (11012762760317/25000000000000 : ℝ)^6247 := by
    have hnat : (5393391507 : ℕ)^8295*25000000000000^6247 ≤ 11012762760317^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393391507 10000000000 11012762760317 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66404957/125000000 : ℝ), (-84924793/400000000 : ℝ), (5393391507/10000000000 : ℝ)] ![(10793702740087/25000000000000 : ℝ), (1596767248147/12500000000000 : ℝ), (11012762760317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66404957/125000000 : ℝ)|^8295 ≤ (10793702740087/25000000000000 : ℝ)^6247
        have hw : |(66404957/125000000 : ℝ)|=(66404957/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84924793/400000000 : ℝ)|^8295 ≤ (1596767248147/12500000000000 : ℝ)^6247
        have hw : |(-84924793/400000000 : ℝ)|=(84924793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393391507/10000000000 : ℝ)|^8295 ≤ (11012762760317/25000000000000 : ℝ)^6247
        have hw : |(5393391507/10000000000 : ℝ)|=(5393391507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656198271/5000000000 : ℝ)*x 0 + (674173939/1250000000 : ℝ)*x 1 + (-2123119843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656198271/5000000000 : ℝ)^8295 ≤ (43174810766099/100000000000000 : ℝ)^6247 := by
    have hnat : (2656198271 : ℕ)^8295*100000000000000^6247 ≤ 43174810766099^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656198271 5000000000 43174810766099 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674173939/1250000000 : ℝ)^8295 ≤ (22025525547747/50000000000000 : ℝ)^6247 := by
    have hnat : (674173939 : ℕ)^8295*50000000000000^6247 ≤ 22025525547747^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674173939 1250000000 22025525547747 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123119843/10000000000 : ℝ)^8295 ≤ (12774138128981/100000000000000 : ℝ)^6247 := by
    have hnat : (2123119843 : ℕ)^8295*100000000000000^6247 ≤ 12774138128981^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123119843 10000000000 12774138128981 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656198271/5000000000 : ℝ), (674173939/1250000000 : ℝ), (-2123119843/10000000000 : ℝ)] ![(43174810766099/100000000000000 : ℝ), (22025525547747/50000000000000 : ℝ), (12774138128981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656198271/5000000000 : ℝ)|^8295 ≤ (43174810766099/100000000000000 : ℝ)^6247
        have hw : |(2656198271/5000000000 : ℝ)|=(2656198271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674173939/1250000000 : ℝ)|^8295 ≤ (22025525547747/50000000000000 : ℝ)^6247
        have hw : |(674173939/1250000000 : ℝ)|=(674173939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123119843/10000000000 : ℝ)|^8295 ≤ (12774138128981/100000000000000 : ℝ)^6247
        have hw : |(-2123119843/10000000000 : ℝ)|=(2123119843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_s8_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092587599/2500000000 : ℝ)*x 0 + (4498486831/10000000000 : ℝ)*x 1 + (169835991/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092587599/2500000000 : ℝ)^8295 ≤ (8329214861689/25000000000000 : ℝ)^6247 := by
    have hnat : (1092587599 : ℕ)^8295*25000000000000^6247 ≤ 8329214861689^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092587599 2500000000 8329214861689 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498486831/10000000000 : ℝ)^8295 ≤ (8655032110349/25000000000000 : ℝ)^6247 := by
    have hnat : (4498486831 : ℕ)^8295*25000000000000^6247 ≤ 8655032110349^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498486831 10000000000 8655032110349 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169835991/400000000 : ℝ)^8295 ≤ (16031506047149/50000000000000 : ℝ)^6247 := by
    have hnat : (169835991 : ℕ)^8295*50000000000000^6247 ≤ 16031506047149^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169835991 400000000 16031506047149 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092587599/2500000000 : ℝ), (4498486831/10000000000 : ℝ), (169835991/400000000 : ℝ)] ![(8329214861689/25000000000000 : ℝ), (8655032110349/25000000000000 : ℝ), (16031506047149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092587599/2500000000 : ℝ)|^8295 ≤ (8329214861689/25000000000000 : ℝ)^6247
        have hw : |(1092587599/2500000000 : ℝ)|=(1092587599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498486831/10000000000 : ℝ)|^8295 ≤ (8655032110349/25000000000000 : ℝ)^6247
        have hw : |(4498486831/10000000000 : ℝ)|=(4498486831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169835991/400000000 : ℝ)|^8295 ≤ (16031506047149/50000000000000 : ℝ)^6247
        have hw : |(169835991/400000000 : ℝ)|=(169835991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11301/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (561/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11299/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (7310835170770087/50000000000000000000 : ℝ) := by
    have hpowers : (11299/100000 : ℝ)^4147 ≤ (7310835170770087/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11299 : ℕ)^4147*50000000000000000000^1024 ≤ 7310835170770087^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11299 100000 7310835170770087 50000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11299/100000 : ℝ)) (X := (7310835170770087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (17552704461349621/50000000000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^4147 ≤ (17552704461349621/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14027 : ℕ)^4147*50000000000000000000^1024 ≤ 17552704461349621^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 17552704461349621 50000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (17552704461349621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007310835170770087/25000000000000000000 : ℝ) ≤ (5000361006560127/5000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25007310835170770087/25000000000000000000 : ℝ)^1024 ≤ (5000361006560127/5000000000000000 : ℝ)^4147 := by
      have hnat : (25007310835170770087 : ℕ)^1024*5000000000000000^4147 ≤ 5000361006560127^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007310835170770087 25000000000000000000 5000361006560127 5000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361006560127/5000000000000000 : ℝ)) (X := (25007310835170770087/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506215884908029927/12500000000000000000 : ℝ) ≤ (10001227658488701/10000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (12506215884908029927/12500000000000000000 : ℝ)^1024 ≤ (10001227658488701/10000000000000000 : ℝ)^4147 := by
      have hnat : (12506215884908029927 : ℕ)^1024*10000000000000000^4147 ≤ 10001227658488701^4147*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506215884908029927 12500000000000000000 10001227658488701 10000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001227658488701/10000000000000000 : ℝ)) (X := (12506215884908029927/12500000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017552704461349621/25000000000000000000 : ℝ) ≤ (2500433325964287/2500000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (25017552704461349621/25000000000000000000 : ℝ)^1024 ≤ (2500433325964287/2500000000000000 : ℝ)^4147 := by
      have hnat : (25017552704461349621 : ℕ)^1024*2500000000000000^4147 ≤ 2500433325964287^4147*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017552704461349621 25000000000000000000 2500433325964287 2500000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500433325964287/2500000000000000 : ℝ)) (X := (25017552704461349621/25000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7310835170770087/50000000000000000000 : ℝ) ≤ ((13635271538877943803/13640000000000000000 : ℝ)+2*(505645368447/272800000000000 : ℝ)*(11299/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (13635271538877943803/13640000000000000000 : ℝ)+2*(505645368447/272800000000000 : ℝ)*(11299/100000 : ℝ)=(5000361006560127/5000000000000000 : ℝ) by norm_num, show 1+2*(7310835170770087/50000000000000000000 : ℝ)=(25007310835170770087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17552704461349621/50000000000000000000 : ℝ)+(7310835170770087/50000000000000000000 : ℝ) ≤ ((13635271538877943803/13640000000000000000 : ℝ)+(505645368447/272800000000000 : ℝ)*((14027/100000 : ℝ)+(11299/100000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (13635271538877943803/13640000000000000000 : ℝ)+(505645368447/272800000000000 : ℝ)*((14027/100000 : ℝ)+(11299/100000 : ℝ))=(10001227658488701/10000000000000000 : ℝ) by norm_num, show 1+(17552704461349621/50000000000000000000 : ℝ)+(7310835170770087/50000000000000000000 : ℝ)=(12506215884908029927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17552704461349621/50000000000000000000 : ℝ) ≤ ((13635271538877943803/13640000000000000000 : ℝ)+2*(505645368447/272800000000000 : ℝ)*(14027/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (13635271538877943803/13640000000000000000 : ℝ)+2*(505645368447/272800000000000 : ℝ)*(14027/100000 : ℝ)=(2500433325964287/2500000000000000 : ℝ) by norm_num, show 1+2*(17552704461349621/50000000000000000000 : ℝ)=(25017552704461349621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13635271538877943803/13640000000000000000 : ℝ)*(X 1 0+X 2 0)+(505645368447/272800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13635271538877943803/13640000000000000000 : ℝ)) (alpha := (505645368447/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13635271538877943803/13640000000000000000 : ℝ)*(X 0 1+X 2 1)+(505645368447/272800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13635271538877943803/13640000000000000000 : ℝ)) (alpha := (505645368447/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13635271538877943803/13640000000000000000 : ℝ)*(X 0 2+X 1 2)+(505645368447/272800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (13635271538877943803/13640000000000000000 : ℝ)) (alpha := (505645368447/272800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-218616361/1000000000 : ℝ)*X 0 0+(269685759/500000000 : ℝ)*X 0 1+(2632552061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336220641/2500000000 : ℝ)*X 1 0+(-2251407253/10000000000 : ℝ)*X 1 1+(65813801/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668110321/1250000000 : ℝ)*X 2 0+(5265104111/10000000000 : ℝ)*X 2 1+(-2251407207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185170257/5000000000 : ℝ)*X 0 0+(2122630463/5000000000 : ℝ)*X 0 1+(89982469/200000000 : ℝ)*X 0 2+(2185170257/5000000000 : ℝ)*X 1 0+(2122630463/5000000000 : ℝ)*X 1 1+(89982469/200000000 : ℝ)*X 1 2+(2185170257/5000000000 : ℝ)*X 2 0+(2122630463/5000000000 : ℝ)*X 2 1+(89982469/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273271077/1250000000 : ℝ)*X 0 0+(5265426603/10000000000 : ℝ)*X 0 1+(539339151/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66404957/125000000 : ℝ)*X 1 0+(-84924793/400000000 : ℝ)*X 1 1+(5393391507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656198271/5000000000 : ℝ)*X 2 0+(674173939/1250000000 : ℝ)*X 2 1+(-2123119843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092587599/2500000000 : ℝ)*X 0 0+(4498486831/10000000000 : ℝ)*X 0 1+(169835991/400000000 : ℝ)*X 0 2+(1092587599/2500000000 : ℝ)*X 1 0+(4498486831/10000000000 : ℝ)*X 1 1+(169835991/400000000 : ℝ)*X 1 2+(1092587599/2500000000 : ℝ)*X 2 0+(4498486831/10000000000 : ℝ)*X 2 1+(169835991/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1429421845724188349831923473/341000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (712122633/100000000000000 : ℝ)*(base19) + (330890203/50000000000000 : ℝ)*(base23) + (3752187/12500000000000 : ℝ)*(lower2) + (22065037/50000000000000 : ℝ)*(upper3) + (9600651/12500000000000 : ℝ)*(upper5) + (2928644963444703/50000000000000 : ℝ)*(major0) + (2928644963444703/50000000000000 : ℝ)*(major1) + (2928644963444703/50000000000000 : ℝ)*(major2) + (6220319085371/80000000000 : ℝ)*(sp0) + (3887709221220709/50000000000000 : ℝ)*(sp1) + (1555083698556729/20000000000000 : ℝ)*(sp2) + (984787592900611/25000000000000 : ℝ)*(sp3) + (202978503/1000000000000 : ℝ)*(sp4) + (10187883873/100000000000000 : ℝ)*(sp7) + (984790139871579/25000000000000 : ℝ)*(f.failure) + (7775419154564051/100000000000000 : ℝ)*(f.sum) + (12476726490561/6820000000000000000000000000 : ℝ)*base65 + (2422429911070075509/682000000000000000000000000000000 : ℝ)*base67 + (1764957790094075509/682000000000000000000000000000000 : ℝ)*base69 + (10590825635812075509/682000000000000000000000000000000 : ℝ)*base71 + (56643409011219/6820000000000000000000000000 : ℝ)*base74 + (7307521078985924491/682000000000000000000000000000000 : ℝ)*base76 + (6978704973156075509/682000000000000000000000000000000 : ℝ)*base77 + (12241803618919924491/682000000000000000000000000000000 : ℝ)*base80 + (27150564578959/6820000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (24323481/2500000000000000000000 : ℝ)*base90 + (24323481/2500000000000000000000 : ℝ)*base92 + (24323481/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5956072965952278778299/852500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249257703/100000000000000 : ℝ)*(base19) + (265949027/20000000000000 : ℝ)*(base23) + (105886553/25000000000000 : ℝ)*(lower1) + (149593521/100000000000000 : ℝ)*(upper3) + (50686017/100000000000000 : ℝ)*(lower4) + (137727977/100000000000000 : ℝ)*(upper5) + (735851332113277/12500000000000 : ℝ)*(major0) + (735851332113277/12500000000000 : ℝ)*(major1) + (735851332113277/12500000000000 : ℝ)*(major2) + (377909463/20000000000000 : ℝ)*(sp2) + (3907303579880957/50000000000000 : ℝ)*(sp4) + (7814605910504211/100000000000000 : ℝ)*(sp5) + (1562920788093893/20000000000000 : ℝ)*(sp6) + (1979506960581989/50000000000000 : ℝ)*(sp7) + (1979506960581989/50000000000000 : ℝ)*(f.failure) + (3907303579880957/50000000000000 : ℝ)*(f.sum) + (3330651399301/1705000000000000000000000000 : ℝ)*base66 + (2228594398847122431/170500000000000000000000000000000 : ℝ)*base67 + (293763258132122431/170500000000000000000000000000000 : ℝ)*base69 + (996289929906877569/170500000000000000000000000000000 : ℝ)*base72 + (1397331128063/213125000000000000000000000 : ℝ)*base73 + (1469158572923622431/170500000000000000000000000000000 : ℝ)*base75 + (432852354601877569/170500000000000000000000000000000 : ℝ)*base78 + (2688607682114377569/170500000000000000000000000000000 : ℝ)*base80 + (968732037069/1705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48530471/5000000000000000000000 : ℝ)*base90 + (48530471/5000000000000000000000 : ℝ)*base92 + (48530471/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1102_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1102_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1102_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1102_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1102_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1102_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
