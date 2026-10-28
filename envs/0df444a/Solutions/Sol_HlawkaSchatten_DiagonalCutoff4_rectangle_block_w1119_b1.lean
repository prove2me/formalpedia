-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:51.979873+00:00
-- url     : https://prove2.me/submissions/950bfa32-6778-4664-ab1d-99562587884d

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
theorem support_rectangle_w1119_s3_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086934809/5000000000 : ℝ)*x 0 + (2715798051/5000000000 : ℝ)*x 1 + (5229871009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086934809/5000000000 : ℝ)^1039 ≤ (13199076601201/100000000000000 : ℝ)^783 := by
    have hnat : (1086934809 : ℕ)^1039*100000000000000^783 ≤ 13199076601201^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086934809 5000000000 13199076601201 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715798051/5000000000 : ℝ)^1039 ≤ (5561252870549/12500000000000 : ℝ)^783 := by
    have hnat : (2715798051 : ℕ)^1039*12500000000000^783 ≤ 5561252870549^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715798051 5000000000 5561252870549 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229871009/10000000000 : ℝ)^1039 ≤ (1322215638027/3125000000000 : ℝ)^783 := by
    have hnat : (5229871009 : ℕ)^1039*3125000000000^783 ≤ 1322215638027^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229871009 10000000000 1322215638027 3125000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086934809/5000000000 : ℝ), (2715798051/5000000000 : ℝ), (5229871009/10000000000 : ℝ)] ![(13199076601201/100000000000000 : ℝ), (5561252870549/12500000000000 : ℝ), (1322215638027/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086934809/5000000000 : ℝ)|^1039 ≤ (13199076601201/100000000000000 : ℝ)^783
        have hw : |(-1086934809/5000000000 : ℝ)|=(1086934809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715798051/5000000000 : ℝ)|^1039 ≤ (5561252870549/12500000000000 : ℝ)^783
        have hw : |(2715798051/5000000000 : ℝ)|=(2715798051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229871009/10000000000 : ℝ)|^1039 ≤ (1322215638027/3125000000000 : ℝ)^783
        have hw : |(5229871009/10000000000 : ℝ)|=(5229871009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5354353777/10000000000 : ℝ)*x 0 + (-1138518827/5000000000 : ℝ)*x 1 + (209194839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354353777/10000000000 : ℝ)^1039 ≤ (4365243537079/10000000000000 : ℝ)^783 := by
    have hnat : (5354353777 : ℕ)^1039*10000000000000^783 ≤ 4365243537079^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354353777 10000000000 4365243537079 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138518827/5000000000 : ℝ)^1039 ≤ (14036664562957/100000000000000 : ℝ)^783 := by
    have hnat : (1138518827 : ℕ)^1039*100000000000000^783 ≤ 14036664562957^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138518827 5000000000 14036664562957 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209194839/400000000 : ℝ)^1039 ≤ (42310900051863/100000000000000 : ℝ)^783 := by
    have hnat : (209194839 : ℕ)^1039*100000000000000^783 ≤ 42310900051863^783*400000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209194839 400000000 42310900051863 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354353777/10000000000 : ℝ), (-1138518827/5000000000 : ℝ), (209194839/400000000 : ℝ)] ![(4365243537079/10000000000000 : ℝ), (14036664562957/100000000000000 : ℝ), (42310900051863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354353777/10000000000 : ℝ)|^1039 ≤ (4365243537079/10000000000000 : ℝ)^783
        have hw : |(5354353777/10000000000 : ℝ)|=(5354353777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138518827/5000000000 : ℝ)|^1039 ≤ (14036664562957/100000000000000 : ℝ)^783
        have hw : |(-1138518827/5000000000 : ℝ)|=(1138518827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209194839/400000000 : ℝ)|^1039 ≤ (42310900051863/100000000000000 : ℝ)^783
        have hw : |(209194839/400000000 : ℝ)|=(209194839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2677176943/5000000000 : ℝ)*x 0 + (2614935539/5000000000 : ℝ)*x 1 + (-18216299/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677176943/5000000000 : ℝ)^1039 ≤ (21826218274987/50000000000000 : ℝ)^783 := by
    have hnat : (2677176943 : ℕ)^1039*50000000000000^783 ≤ 21826218274987^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677176943 5000000000 21826218274987 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614935539/5000000000 : ℝ)^1039 ≤ (42310901157601/100000000000000 : ℝ)^783 := by
    have hnat : (2614935539 : ℕ)^1039*100000000000000^783 ≤ 42310901157601^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614935539 5000000000 42310901157601 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18216299/80000000 : ℝ)^1039 ≤ (219322848137/1562500000000 : ℝ)^783 := by
    have hnat : (18216299 : ℕ)^1039*1562500000000^783 ≤ 219322848137^783*80000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18216299 80000000 219322848137 1562500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677176943/5000000000 : ℝ), (2614935539/5000000000 : ℝ), (-18216299/80000000 : ℝ)] ![(21826218274987/50000000000000 : ℝ), (42310901157601/100000000000000 : ℝ), (219322848137/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677176943/5000000000 : ℝ)|^1039 ≤ (21826218274987/50000000000000 : ℝ)^783
        have hw : |(2677176943/5000000000 : ℝ)|=(2677176943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614935539/5000000000 : ℝ)|^1039 ≤ (42310901157601/100000000000000 : ℝ)^783
        have hw : |(2614935539/5000000000 : ℝ)|=(2614935539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18216299/80000000 : ℝ)|^1039 ≤ (219322848137/1562500000000 : ℝ)^783
        have hw : |(-18216299/80000000 : ℝ)|=(18216299/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (873102719/2000000000 : ℝ)*x 0 + (834064227/2000000000 : ℝ)*x 1 + (114245941/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873102719/2000000000 : ℝ)^1039 ≤ (33292449647563/100000000000000 : ℝ)^783 := by
    have hnat : (873102719 : ℕ)^1039*100000000000000^783 ≤ 33292449647563^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873102719 2000000000 33292449647563 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834064227/2000000000 : ℝ)^1039 ≤ (31331761658191/100000000000000 : ℝ)^783 := by
    have hnat : (834064227 : ℕ)^1039*100000000000000^783 ≤ 31331761658191^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834064227 2000000000 31331761658191 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114245941/250000000 : ℝ)^1039 ≤ (3537578867753/10000000000000 : ℝ)^783 := by
    have hnat : (114245941 : ℕ)^1039*10000000000000^783 ≤ 3537578867753^783*250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114245941 250000000 3537578867753 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873102719/2000000000 : ℝ), (834064227/2000000000 : ℝ), (114245941/250000000 : ℝ)] ![(33292449647563/100000000000000 : ℝ), (31331761658191/100000000000000 : ℝ), (3537578867753/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873102719/2000000000 : ℝ)|^1039 ≤ (33292449647563/100000000000000 : ℝ)^783
        have hw : |(873102719/2000000000 : ℝ)|=(873102719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834064227/2000000000 : ℝ)|^1039 ≤ (31331761658191/100000000000000 : ℝ)^783
        have hw : |(834064227/2000000000 : ℝ)|=(834064227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114245941/250000000 : ℝ)|^1039 ≤ (3537578867753/10000000000000 : ℝ)^783
        have hw : |(114245941/250000000 : ℝ)|=(114245941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086944593/5000000000 : ℝ)*x 0 + (653833331/1250000000 : ℝ)*x 1 + (678849463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086944593/5000000000 : ℝ)^1039 ≤ (1649904282169/12500000000000 : ℝ)^783 := by
    have hnat : (1086944593 : ℕ)^1039*12500000000000^783 ≤ 1649904282169^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086944593 5000000000 1649904282169 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653833331/1250000000 : ℝ)^1039 ≤ (10579860517537/25000000000000 : ℝ)^783 := by
    have hnat : (653833331 : ℕ)^1039*25000000000000^783 ≤ 10579860517537^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653833331 1250000000 10579860517537 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678849463/1250000000 : ℝ)^1039 ≤ (889626473219/2000000000000 : ℝ)^783 := by
    have hnat : (678849463 : ℕ)^1039*2000000000000^783 ≤ 889626473219^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678849463 1250000000 889626473219 2000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086944593/5000000000 : ℝ), (653833331/1250000000 : ℝ), (678849463/1250000000 : ℝ)] ![(1649904282169/12500000000000 : ℝ), (10579860517537/25000000000000 : ℝ), (889626473219/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086944593/5000000000 : ℝ)|^1039 ≤ (1649904282169/12500000000000 : ℝ)^783
        have hw : |(-1086944593/5000000000 : ℝ)|=(1086944593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653833331/1250000000 : ℝ)|^1039 ≤ (10579860517537/25000000000000 : ℝ)^783
        have hw : |(653833331/1250000000 : ℝ)|=(653833331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678849463/1250000000 : ℝ)|^1039 ≤ (889626473219/2000000000000 : ℝ)^783
        have hw : |(678849463/1250000000 : ℝ)|=(678849463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651667029/5000000000 : ℝ)*x 0 + (-1038056539/5000000000 : ℝ)*x 1 + (5430795913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651667029/5000000000 : ℝ)^1039 ≤ (10775338798833/25000000000000 : ℝ)^783 := by
    have hnat : (2651667029 : ℕ)^1039*25000000000000^783 ≤ 10775338798833^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651667029 5000000000 10775338798833 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038056539/5000000000 : ℝ)^1039 ≤ (3104329713497/25000000000000 : ℝ)^783 := by
    have hnat : (1038056539 : ℕ)^1039*25000000000000^783 ≤ 3104329713497^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038056539 5000000000 3104329713497 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430795913/10000000000 : ℝ)^1039 ≤ (22240662966229/50000000000000 : ℝ)^783 := by
    have hnat : (5430795913 : ℕ)^1039*50000000000000^783 ≤ 22240662966229^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430795913 10000000000 22240662966229 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651667029/5000000000 : ℝ), (-1038056539/5000000000 : ℝ), (5430795913/10000000000 : ℝ)] ![(10775338798833/25000000000000 : ℝ), (3104329713497/25000000000000 : ℝ), (22240662966229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651667029/5000000000 : ℝ)|^1039 ≤ (10775338798833/25000000000000 : ℝ)^783
        have hw : |(2651667029/5000000000 : ℝ)|=(2651667029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038056539/5000000000 : ℝ)|^1039 ≤ (3104329713497/25000000000000 : ℝ)^783
        have hw : |(-1038056539/5000000000 : ℝ)|=(1038056539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430795913/10000000000 : ℝ)|^1039 ≤ (22240662966229/50000000000000 : ℝ)^783
        have hw : |(5430795913/10000000000 : ℝ)|=(5430795913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5303334797/10000000000 : ℝ)*x 0 + (2715397993/5000000000 : ℝ)*x 1 + (-83044479/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303334797/10000000000 : ℝ)^1039 ≤ (43101363164999/100000000000000 : ℝ)^783 := by
    have hnat : (5303334797 : ℕ)^1039*100000000000000^783 ≤ 43101363164999^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303334797 10000000000 43101363164999 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715397993/5000000000 : ℝ)^1039 ≤ (1390041460183/3125000000000 : ℝ)^783 := by
    have hnat : (2715397993 : ℕ)^1039*3125000000000^783 ≤ 1390041460183^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715397993 5000000000 1390041460183 3125000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83044479/400000000 : ℝ)^1039 ≤ (12417310099997/100000000000000 : ℝ)^783 := by
    have hnat : (83044479 : ℕ)^1039*100000000000000^783 ≤ 12417310099997^783*400000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83044479 400000000 12417310099997 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303334797/10000000000 : ℝ), (2715397993/5000000000 : ℝ), (-83044479/400000000 : ℝ)] ![(43101363164999/100000000000000 : ℝ), (1390041460183/3125000000000 : ℝ), (12417310099997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303334797/10000000000 : ℝ)|^1039 ≤ (43101363164999/100000000000000 : ℝ)^783
        have hw : |(5303334797/10000000000 : ℝ)|=(5303334797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715397993/5000000000 : ℝ)|^1039 ≤ (1390041460183/3125000000000 : ℝ)^783
        have hw : |(2715397993/5000000000 : ℝ)|=(2715397993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83044479/400000000 : ℝ)|^1039 ≤ (12417310099997/100000000000000 : ℝ)^783
        have hw : |(-83044479/400000000 : ℝ)|=(83044479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s3_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2182775723/5000000000 : ℝ)*x 0 + (913652517/2000000000 : ℝ)*x 1 + (2085952701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182775723/5000000000 : ℝ)^1039 ≤ (33292832685831/100000000000000 : ℝ)^783 := by
    have hnat : (2182775723 : ℕ)^1039*100000000000000^783 ≤ 33292832685831^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182775723 5000000000 33292832685831 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (913652517/2000000000 : ℝ)^1039 ≤ (1414384418807/4000000000000 : ℝ)^783 := by
    have hnat : (913652517 : ℕ)^1039*4000000000000^783 ≤ 1414384418807^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913652517 2000000000 1414384418807 4000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085952701/5000000000 : ℝ)^1039 ≤ (31347556833271/100000000000000 : ℝ)^783 := by
    have hnat : (2085952701 : ℕ)^1039*100000000000000^783 ≤ 31347556833271^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085952701 5000000000 31347556833271 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182775723/5000000000 : ℝ), (913652517/2000000000 : ℝ), (2085952701/5000000000 : ℝ)] ![(33292832685831/100000000000000 : ℝ), (1414384418807/4000000000000 : ℝ), (31347556833271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182775723/5000000000 : ℝ)|^1039 ≤ (33292832685831/100000000000000 : ℝ)^783
        have hw : |(2182775723/5000000000 : ℝ)|=(2182775723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(913652517/2000000000 : ℝ)|^1039 ≤ (1414384418807/4000000000000 : ℝ)^783
        have hw : |(913652517/2000000000 : ℝ)|=(913652517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085952701/5000000000 : ℝ)|^1039 ≤ (31347556833271/100000000000000 : ℝ)^783
        have hw : |(2085952701/5000000000 : ℝ)|=(2085952701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2113/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7417/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4143/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1793/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4143/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1793/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4143/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1793/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4143/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1793/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4143/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1793/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4143/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1793/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1793/20000 : ℝ) ^ (8311/2048 : ℝ) ≤ (5614855957493289/100000000000000000000 : ℝ) := by
    have hpowers : (1793/20000 : ℝ)^8311 ≤ (5614855957493289/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1793 : ℕ)^8311*100000000000000000000^2048 ≤ 5614855957493289^2048*20000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1793 20000 5614855957493289 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1793/20000 : ℝ)) (X := (5614855957493289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4143/25000 : ℝ) ^ (8311/2048 : ℝ) ≤ (33971217892577797/50000000000000000000 : ℝ) := by
    have hpowers : (4143/25000 : ℝ)^8311 ≤ (33971217892577797/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4143 : ℕ)^8311*50000000000000000000^2048 ≤ 33971217892577797^2048*25000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4143 25000 33971217892577797 50000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4143/25000 : ℝ)) (X := (33971217892577797/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005614855957493289/50000000000000000000 : ℝ) ≤ (5000138355654831/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50005614855957493289/50000000000000000000 : ℝ)^2048 ≤ (5000138355654831/5000000000000000 : ℝ)^8311 := by
      have hnat : (50005614855957493289 : ℕ)^2048*5000000000000000^8311 ≤ 5000138355654831^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005614855957493289 50000000000000000000 5000138355654831 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138355654831/5000000000000000 : ℝ)) (X := (50005614855957493289/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073557291742648883/100000000000000000000 : ℝ) ≤ (2500453024904097/2500000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (100073557291742648883/100000000000000000000 : ℝ)^2048 ≤ (2500453024904097/2500000000000000 : ℝ)^8311 := by
      have hnat : (100073557291742648883 : ℕ)^2048*2500000000000000^8311 ≤ 2500453024904097^8311*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073557291742648883 100000000000000000000 2500453024904097 2500000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500453024904097/2500000000000000 : ℝ)) (X := (100073557291742648883/100000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033971217892577797/25000000000000000000 : ℝ) ≤ (5001673743961557/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (25033971217892577797/25000000000000000000 : ℝ)^2048 ≤ (5001673743961557/5000000000000000 : ℝ)^8311 := by
      have hnat : (25033971217892577797 : ℕ)^2048*5000000000000000^8311 ≤ 5001673743961557^8311*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033971217892577797 25000000000000000000 5001673743961557 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001673743961557/5000000000000000 : ℝ)) (X := (25033971217892577797/25000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5614855957493289/100000000000000000000 : ℝ) ≤ ((38022287715296500827/38035000000000000000 : ℝ)+2*(767694153363/380350000000000 : ℝ)*(1793/20000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (38022287715296500827/38035000000000000000 : ℝ)+2*(767694153363/380350000000000 : ℝ)*(1793/20000 : ℝ)=(5000138355654831/5000000000000000 : ℝ) by norm_num, show 1+2*(5614855957493289/100000000000000000000 : ℝ)=(50005614855957493289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33971217892577797/50000000000000000000 : ℝ)+(5614855957493289/100000000000000000000 : ℝ) ≤ ((38022287715296500827/38035000000000000000 : ℝ)+(767694153363/380350000000000 : ℝ)*((4143/25000 : ℝ)+(1793/20000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (38022287715296500827/38035000000000000000 : ℝ)+(767694153363/380350000000000 : ℝ)*((4143/25000 : ℝ)+(1793/20000 : ℝ))=(2500453024904097/2500000000000000 : ℝ) by norm_num, show 1+(33971217892577797/50000000000000000000 : ℝ)+(5614855957493289/100000000000000000000 : ℝ)=(100073557291742648883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33971217892577797/50000000000000000000 : ℝ) ≤ ((38022287715296500827/38035000000000000000 : ℝ)+2*(767694153363/380350000000000 : ℝ)*(4143/25000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (38022287715296500827/38035000000000000000 : ℝ)+2*(767694153363/380350000000000 : ℝ)*(4143/25000 : ℝ)=(5001673743961557/5000000000000000 : ℝ) by norm_num, show 1+2*(33971217892577797/50000000000000000000 : ℝ)=(25033971217892577797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38022287715296500827/38035000000000000000 : ℝ)*(X 1 0+X 2 0)+(767694153363/380350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (1793/20000 : ℝ)) (hi := (4143/25000 : ℝ)) (c := (38022287715296500827/38035000000000000000 : ℝ)) (alpha := (767694153363/380350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38022287715296500827/38035000000000000000 : ℝ)*(X 0 1+X 2 1)+(767694153363/380350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (1793/20000 : ℝ)) (hi := (4143/25000 : ℝ)) (c := (38022287715296500827/38035000000000000000 : ℝ)) (alpha := (767694153363/380350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38022287715296500827/38035000000000000000 : ℝ)*(X 0 2+X 1 2)+(767694153363/380350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (1793/20000 : ℝ)) (hi := (4143/25000 : ℝ)) (c := (38022287715296500827/38035000000000000000 : ℝ)) (alpha := (767694153363/380350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1086934809/5000000000 : ℝ)*X 0 0+(2715798051/5000000000 : ℝ)*X 0 1+(5229871009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354353777/10000000000 : ℝ)*X 1 0+(-1138518827/5000000000 : ℝ)*X 1 1+(209194839/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677176943/5000000000 : ℝ)*X 2 0+(2614935539/5000000000 : ℝ)*X 2 1+(-18216299/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873102719/2000000000 : ℝ)*X 0 0+(834064227/2000000000 : ℝ)*X 0 1+(114245941/250000000 : ℝ)*X 0 2+(873102719/2000000000 : ℝ)*X 1 0+(834064227/2000000000 : ℝ)*X 1 1+(114245941/250000000 : ℝ)*X 1 2+(873102719/2000000000 : ℝ)*X 2 0+(834064227/2000000000 : ℝ)*X 2 1+(114245941/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086944593/5000000000 : ℝ)*X 0 0+(653833331/1250000000 : ℝ)*X 0 1+(678849463/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651667029/5000000000 : ℝ)*X 1 0+(-1038056539/5000000000 : ℝ)*X 1 1+(5430795913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303334797/10000000000 : ℝ)*X 2 0+(2715397993/5000000000 : ℝ)*X 2 1+(-83044479/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182775723/5000000000 : ℝ)*X 0 0+(913652517/2000000000 : ℝ)*X 0 1+(2085952701/5000000000 : ℝ)*X 0 2+(2182775723/5000000000 : ℝ)*X 1 0+(913652517/2000000000 : ℝ)*X 1 1+(2085952701/5000000000 : ℝ)*X 1 2+(2182775723/5000000000 : ℝ)*X 2 0+(913652517/2000000000 : ℝ)*X 2 1+(2085952701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9122218965573113584883186877/950875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2396388141/100000000000000 : ℝ)*(base19) + (281559373/12500000000000 : ℝ)*(base23) + (32772767/25000000000000 : ℝ)*(lower2) + (16373803/10000000000000 : ℝ)*(upper3) + (35405919/12500000000000 : ℝ)*(upper5) + (1865099213293717/50000000000000 : ℝ)*(major0) + (1865099213293717/50000000000000 : ℝ)*(major1) + (1865099213293717/50000000000000 : ℝ)*(major2) + (4957282216069243/100000000000000 : ℝ)*(sp0) + (495732772395247/10000000000000 : ℝ)*(sp1) + (4957327867865627/100000000000000 : ℝ)*(sp2) + (312880756404841/12500000000000 : ℝ)*(sp3) + (47904271369/100000000000000 : ℝ)*(sp4) + (20361812199/100000000000000 : ℝ)*(sp7) + (1251533206525463/50000000000000 : ℝ)*(f.failure) + (4957330120340611/100000000000000 : ℝ)*(f.sum) + (29258773489687/19017500000000000000000000000 : ℝ)*base65 + (19653554347726246041/1901750000000000000000000000000000 : ℝ)*base68 + (31039927393180246041/1901750000000000000000000000000000 : ℝ)*base70 + (11233350267729503959/1901750000000000000000000000000000 : ℝ)*base71 + (273222323674941/38035000000000000000000000000 : ℝ)*base74 + (881168315767503959/1901750000000000000000000000000000 : ℝ)*base75 + (14136560183401496041/1901750000000000000000000000000000 : ℝ)*base78 + (18944475464940246041/1901750000000000000000000000000000 : ℝ)*base80 + (322668830765671/38035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2664119/1250000000000000000000 : ℝ)*base90 + (2664119/1250000000000000000000 : ℝ)*base92 + (2664119/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1043697929725116341083668483/190175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321327271/25000000000000 : ℝ)*(base19) + (1302525367/50000000000000 : ℝ)*(base23) + (25219497/20000000000000 : ℝ)*(upper2) + (36046241/12500000000000 : ℝ)*(upper3) + (8776091/10000000000000 : ℝ)*(upper5) + (751975654982157/20000000000000 : ℝ)*(major0) + (751975654982157/20000000000000 : ℝ)*(major1) + (751975654982157/20000000000000 : ℝ)*(major2) + (5018622913/25000000000000 : ℝ)*(sp1) + (1880201201/3125000000000 : ℝ)*(sp2) + (4996773953936449/100000000000000 : ℝ)*(sp4) + (4996752594135713/100000000000000 : ℝ)*(sp5) + (1249177795611821/25000000000000 : ℝ)*(sp6) + (2522982412948709/100000000000000 : ℝ)*(sp7) + (2522982412948709/100000000000000 : ℝ)*(f.failure) + (4996773953936449/100000000000000 : ℝ)*(f.sum) + (1867701734541/3803500000000000000000000000 : ℝ)*base65 + (1530536936697943839/760700000000000000000000000000000 : ℝ)*base67 + (7029458170200043839/760700000000000000000000000000000 : ℝ)*base69 + (1799854818579443839/760700000000000000000000000000000 : ℝ)*base71 + (22002812895019/7607000000000000000000000000 : ℝ)*base74 + (2857683086118943839/760700000000000000000000000000000 : ℝ)*base75 + (4883652637060043839/760700000000000000000000000000000 : ℝ)*base77 + (8581006020119656161/760700000000000000000000000000000 : ℝ)*base80 + (324223190589/1901750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6216517/2500000000000000000000 : ℝ)*base90 + (6216517/2500000000000000000000 : ℝ)*base92 + (6216517/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1119_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7417/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s4_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177063831/10000000000 : ℝ)*x 0 + (270151141/500000000 : ℝ)*x 1 + (2628177709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177063831/10000000000 : ℝ)^1039 ≤ (6612408995371/50000000000000 : ℝ)^783 := by
    have hnat : (2177063831 : ℕ)^1039*50000000000000^783 ≤ 6612408995371^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177063831 10000000000 6612408995371 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270151141/500000000 : ℝ)^1039 ≤ (44179727809807/100000000000000 : ℝ)^783 := by
    have hnat : (270151141 : ℕ)^1039*100000000000000^783 ≤ 44179727809807^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270151141 500000000 44179727809807 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628177709/5000000000 : ℝ)^1039 ≤ (42595454179773/100000000000000 : ℝ)^783 := by
    have hnat : (2628177709 : ℕ)^1039*100000000000000^783 ≤ 42595454179773^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628177709 5000000000 42595454179773 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177063831/10000000000 : ℝ), (270151141/500000000 : ℝ), (2628177709/5000000000 : ℝ)] ![(6612408995371/50000000000000 : ℝ), (44179727809807/100000000000000 : ℝ), (42595454179773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177063831/10000000000 : ℝ)|^1039 ≤ (6612408995371/50000000000000 : ℝ)^783
        have hw : |(-2177063831/10000000000 : ℝ)|=(2177063831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270151141/500000000 : ℝ)|^1039 ≤ (44179727809807/100000000000000 : ℝ)^783
        have hw : |(270151141/500000000 : ℝ)|=(270151141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628177709/5000000000 : ℝ)|^1039 ≤ (42595454179773/100000000000000 : ℝ)^783
        have hw : |(2628177709/5000000000 : ℝ)|=(2628177709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347235183/10000000000 : ℝ)*x 0 + (-90064661/400000000 : ℝ)*x 1 + (1314088881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347235183/10000000000 : ℝ)^1039 ≤ (8715088340991/20000000000000 : ℝ)^783 := by
    have hnat : (5347235183 : ℕ)^1039*20000000000000^783 ≤ 8715088340991^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347235183 10000000000 8715088340991 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90064661/400000000 : ℝ)^1039 ≤ (13829102967033/100000000000000 : ℝ)^783 := by
    have hnat : (90064661 : ℕ)^1039*100000000000000^783 ≤ 13829102967033^783*400000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90064661 400000000 13829102967033 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314088881/2500000000 : ℝ)^1039 ≤ (21297727659799/50000000000000 : ℝ)^783 := by
    have hnat : (1314088881 : ℕ)^1039*50000000000000^783 ≤ 21297727659799^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314088881 2500000000 21297727659799 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347235183/10000000000 : ℝ), (-90064661/400000000 : ℝ), (1314088881/2500000000 : ℝ)] ![(8715088340991/20000000000000 : ℝ), (13829102967033/100000000000000 : ℝ), (21297727659799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347235183/10000000000 : ℝ)|^1039 ≤ (8715088340991/20000000000000 : ℝ)^783
        have hw : |(5347235183/10000000000 : ℝ)|=(5347235183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90064661/400000000 : ℝ)|^1039 ≤ (13829102967033/100000000000000 : ℝ)^783
        have hw : |(-90064661/400000000 : ℝ)|=(90064661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314088881/2500000000 : ℝ)|^1039 ≤ (21297727659799/50000000000000 : ℝ)^783
        have hw : |(1314088881/2500000000 : ℝ)|=(1314088881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167101093/312500000 : ℝ)*x 0 + (5256355301/10000000000 : ℝ)*x 1 + (-2251617093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167101093/312500000 : ℝ)^1039 ≤ (136173248333/312500000000 : ℝ)^783 := by
    have hnat : (167101093 : ℕ)^1039*312500000000^783 ≤ 136173248333^783*312500000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167101093 312500000 136173248333 312500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256355301/10000000000 : ℝ)^1039 ≤ (665553951901/1562500000000 : ℝ)^783 := by
    have hnat : (5256355301 : ℕ)^1039*1562500000000^783 ≤ 665553951901^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256355301 10000000000 665553951901 1562500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251617093/10000000000 : ℝ)^1039 ≤ (3457276899047/25000000000000 : ℝ)^783 := by
    have hnat : (2251617093 : ℕ)^1039*25000000000000^783 ≤ 3457276899047^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251617093 10000000000 3457276899047 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167101093/312500000 : ℝ), (5256355301/10000000000 : ℝ), (-2251617093/10000000000 : ℝ)] ![(136173248333/312500000000 : ℝ), (665553951901/1562500000000 : ℝ), (3457276899047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167101093/312500000 : ℝ)|^1039 ≤ (136173248333/312500000000 : ℝ)^783
        have hw : |(167101093/312500000 : ℝ)|=(167101093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256355301/10000000000 : ℝ)|^1039 ≤ (665553951901/1562500000000 : ℝ)^783
        have hw : |(5256355301/10000000000 : ℝ)|=(5256355301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251617093/10000000000 : ℝ)|^1039 ≤ (3457276899047/25000000000000 : ℝ)^783
        have hw : |(-2251617093/10000000000 : ℝ)|=(2251617093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4367416637/10000000000 : ℝ)*x 0 + (4224593883/10000000000 : ℝ)*x 1 + (4515069939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367416637/10000000000 : ℝ)^1039 ≤ (3331170908113/10000000000000 : ℝ)^783 := by
    have hnat : (4367416637 : ℕ)^1039*10000000000000^783 ≤ 3331170908113^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367416637 10000000000 3331170908113 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224593883/10000000000 : ℝ)^1039 ≤ (31873976243769/100000000000000 : ℝ)^783 := by
    have hnat : (4224593883 : ℕ)^1039*100000000000000^783 ≤ 31873976243769^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224593883 10000000000 31873976243769 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515069939/10000000000 : ℝ)^1039 ≤ (34814314662437/100000000000000 : ℝ)^783 := by
    have hnat : (4515069939 : ℕ)^1039*100000000000000^783 ≤ 34814314662437^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515069939 10000000000 34814314662437 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367416637/10000000000 : ℝ), (4224593883/10000000000 : ℝ), (4515069939/10000000000 : ℝ)] ![(3331170908113/10000000000000 : ℝ), (31873976243769/100000000000000 : ℝ), (34814314662437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367416637/10000000000 : ℝ)|^1039 ≤ (3331170908113/10000000000000 : ℝ)^783
        have hw : |(4367416637/10000000000 : ℝ)|=(4367416637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224593883/10000000000 : ℝ)|^1039 ≤ (31873976243769/100000000000000 : ℝ)^783
        have hw : |(4224593883/10000000000 : ℝ)|=(4224593883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515069939/10000000000 : ℝ)|^1039 ≤ (34814314662437/100000000000000 : ℝ)^783
        have hw : |(4515069939/10000000000 : ℝ)|=(4515069939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088535543/5000000000 : ℝ)*x 0 + (2628388341/5000000000 : ℝ)*x 1 + (5402599929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088535543/5000000000 : ℝ)^1039 ≤ (6612438235547/50000000000000 : ℝ)^783 := by
    have hnat : (1088535543 : ℕ)^1039*50000000000000^783 ≤ 6612438235547^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088535543 5000000000 6612438235547 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628388341/5000000000 : ℝ)^1039 ≤ (1064999602969/2500000000000 : ℝ)^783 := by
    have hnat : (2628388341 : ℕ)^1039*2500000000000^783 ≤ 1064999602969^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628388341 5000000000 1064999602969 2500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402599929/10000000000 : ℝ)^1039 ≤ (22087569696271/50000000000000 : ℝ)^783 := by
    have hnat : (5402599929 : ℕ)^1039*50000000000000^783 ≤ 22087569696271^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402599929 10000000000 22087569696271 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088535543/5000000000 : ℝ), (2628388341/5000000000 : ℝ), (5402599929/10000000000 : ℝ)] ![(6612438235547/50000000000000 : ℝ), (1064999602969/2500000000000 : ℝ), (22087569696271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088535543/5000000000 : ℝ)|^1039 ≤ (6612438235547/50000000000000 : ℝ)^783
        have hw : |(-1088535543/5000000000 : ℝ)|=(1088535543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628388341/5000000000 : ℝ)|^1039 ≤ (1064999602969/2500000000000 : ℝ)^783
        have hw : |(2628388341/5000000000 : ℝ)|=(2628388341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402599929/10000000000 : ℝ)|^1039 ≤ (22087569696271/50000000000000 : ℝ)^783
        have hw : |(5402599929/10000000000 : ℝ)|=(5402599929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331883869/625000000 : ℝ)*x 0 + (-2105372519/10000000000 : ℝ)*x 1 + (2701300007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331883869/625000000 : ℝ)^1039 ≤ (21587394544021/50000000000000 : ℝ)^783 := by
    have hnat : (331883869 : ℕ)^1039*50000000000000^783 ≤ 21587394544021^783*625000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331883869 625000000 21587394544021 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105372519/10000000000 : ℝ)^1039 ≤ (12650070585503/100000000000000 : ℝ)^783 := by
    have hnat : (2105372519 : ℕ)^1039*100000000000000^783 ≤ 12650070585503^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105372519 10000000000 12650070585503 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701300007/5000000000 : ℝ)^1039 ≤ (4417514031479/10000000000000 : ℝ)^783 := by
    have hnat : (2701300007 : ℕ)^1039*10000000000000^783 ≤ 4417514031479^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701300007 5000000000 4417514031479 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331883869/625000000 : ℝ), (-2105372519/10000000000 : ℝ), (2701300007/5000000000 : ℝ)] ![(21587394544021/50000000000000 : ℝ), (12650070585503/100000000000000 : ℝ), (4417514031479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331883869/625000000 : ℝ)|^1039 ≤ (21587394544021/50000000000000 : ℝ)^783
        have hw : |(331883869/625000000 : ℝ)|=(331883869/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105372519/10000000000 : ℝ)|^1039 ≤ (12650070585503/100000000000000 : ℝ)^783
        have hw : |(-2105372519/10000000000 : ℝ)|=(2105372519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701300007/5000000000 : ℝ)|^1039 ≤ (4417514031479/10000000000000 : ℝ)^783
        have hw : |(2701300007/5000000000 : ℝ)|=(2701300007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062028397/2000000000 : ℝ)*x 0 + (675325007/1250000000 : ℝ)*x 1 + (-32896443/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062028397/2000000000 : ℝ)^1039 ≤ (5396848745243/12500000000000 : ℝ)^783 := by
    have hnat : (1062028397 : ℕ)^1039*12500000000000^783 ≤ 5396848745243^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062028397 2000000000 5396848745243 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675325007/1250000000 : ℝ)^1039 ≤ (4417514077049/10000000000000 : ℝ)^783 := by
    have hnat : (675325007 : ℕ)^1039*10000000000000^783 ≤ 4417514077049^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675325007 1250000000 4417514077049 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32896443/156250000 : ℝ)^1039 ≤ (1581258656753/12500000000000 : ℝ)^783 := by
    have hnat : (32896443 : ℕ)^1039*12500000000000^783 ≤ 1581258656753^783*156250000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32896443 156250000 1581258656753 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062028397/2000000000 : ℝ), (675325007/1250000000 : ℝ), (-32896443/156250000 : ℝ)] ![(5396848745243/12500000000000 : ℝ), (4417514077049/10000000000000 : ℝ), (1581258656753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062028397/2000000000 : ℝ)|^1039 ≤ (5396848745243/12500000000000 : ℝ)^783
        have hw : |(1062028397/2000000000 : ℝ)|=(1062028397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675325007/1250000000 : ℝ)|^1039 ≤ (4417514077049/10000000000000 : ℝ)^783
        have hw : |(675325007/1250000000 : ℝ)|=(675325007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32896443/156250000 : ℝ)|^1039 ≤ (1581258656753/12500000000000 : ℝ)^783
        have hw : |(-32896443/156250000 : ℝ)|=(32896443/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s4_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4367431743/10000000000 : ℝ)*x 0 + (2257117593/5000000000 : ℝ)*x 1 + (211271583/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367431743/10000000000 : ℝ)^1039 ≤ (4163982746247/12500000000000 : ℝ)^783 := by
    have hnat : (4367431743 : ℕ)^1039*12500000000000^783 ≤ 4163982746247^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367431743 10000000000 4163982746247 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257117593/5000000000 : ℝ)^1039 ≤ (34805773990979/100000000000000 : ℝ)^783 := by
    have hnat : (2257117593 : ℕ)^1039*100000000000000^783 ≤ 34805773990979^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257117593 5000000000 34805773990979 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211271583/500000000 : ℝ)^1039 ≤ (31882364034291/100000000000000 : ℝ)^783 := by
    have hnat : (211271583 : ℕ)^1039*100000000000000^783 ≤ 31882364034291^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211271583 500000000 31882364034291 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367431743/10000000000 : ℝ), (2257117593/5000000000 : ℝ), (211271583/500000000 : ℝ)] ![(4163982746247/12500000000000 : ℝ), (34805773990979/100000000000000 : ℝ), (31882364034291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367431743/10000000000 : ℝ)|^1039 ≤ (4163982746247/12500000000000 : ℝ)^783
        have hw : |(4367431743/10000000000 : ℝ)|=(4367431743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257117593/5000000000 : ℝ)|^1039 ≤ (34805773990979/100000000000000 : ℝ)^783
        have hw : |(2257117593/5000000000 : ℝ)|=(2257117593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211271583/500000000 : ℝ)|^1039 ≤ (31882364034291/100000000000000 : ℝ)^783
        have hw : |(211271583/500000000 : ℝ)|=(211271583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7417/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7417/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7417/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7417/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7417/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7417/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7417/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2113/20000 : ℝ) ^ (8311/2048 : ℝ) ≤ (5466753475277713/50000000000000000000 : ℝ) := by
    have hpowers : (2113/20000 : ℝ)^8311 ≤ (5466753475277713/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2113 : ℕ)^8311*50000000000000000000^2048 ≤ 5466753475277713^2048*20000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2113 20000 5466753475277713 50000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2113/20000 : ℝ)) (X := (5466753475277713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7417/50000 : ℝ) ^ (8311/2048 : ℝ) ≤ (43338978649660997/100000000000000000000 : ℝ) := by
    have hpowers : (7417/50000 : ℝ)^8311 ≤ (43338978649660997/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7417 : ℕ)^8311*100000000000000000000^2048 ≤ 43338978649660997^2048*50000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7417 50000 43338978649660997 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7417/50000 : ℝ)) (X := (43338978649660997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005466753475277713/25000000000000000000 : ℝ) ≤ (5000269401727209/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (25005466753475277713/25000000000000000000 : ℝ)^2048 ≤ (5000269401727209/5000000000000000 : ℝ)^8311 := by
      have hnat : (25005466753475277713 : ℕ)^2048*5000000000000000^8311 ≤ 5000269401727209^8311*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005466753475277713 25000000000000000000 5000269401727209 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269401727209/5000000000000000 : ℝ)) (X := (25005466753475277713/25000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054272485600216423/100000000000000000000 : ℝ) ≤ (2000267422279603/2000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (100054272485600216423/100000000000000000000 : ℝ)^2048 ≤ (2000267422279603/2000000000000000 : ℝ)^8311 := by
      have hnat : (100054272485600216423 : ℕ)^2048*2000000000000000^8311 ≤ 2000267422279603^8311*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054272485600216423 100000000000000000000 2000267422279603 2000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000267422279603/2000000000000000 : ℝ)) (X := (100054272485600216423/100000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043338978649660997/50000000000000000000 : ℝ) ≤ (2500533854835403/2500000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50043338978649660997/50000000000000000000 : ℝ)^2048 ≤ (2500533854835403/2500000000000000 : ℝ)^8311 := by
      have hnat : (50043338978649660997 : ℕ)^2048*2500000000000000^8311 ≤ 2500533854835403^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043338978649660997 50000000000000000000 2500533854835403 2500000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500533854835403/2500000000000000 : ℝ)) (X := (50043338978649660997/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5466753475277713/50000000000000000000 : ℝ) ≤ ((5334428988137338229/5336250000000000000 : ℝ)+2*(798307943597/426900000000000 : ℝ)*(2113/20000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (5334428988137338229/5336250000000000000 : ℝ)+2*(798307943597/426900000000000 : ℝ)*(2113/20000 : ℝ)=(5000269401727209/5000000000000000 : ℝ) by norm_num, show 1+2*(5466753475277713/50000000000000000000 : ℝ)=(25005466753475277713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43338978649660997/100000000000000000000 : ℝ)+(5466753475277713/50000000000000000000 : ℝ) ≤ ((5334428988137338229/5336250000000000000 : ℝ)+(798307943597/426900000000000 : ℝ)*((7417/50000 : ℝ)+(2113/20000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (5334428988137338229/5336250000000000000 : ℝ)+(798307943597/426900000000000 : ℝ)*((7417/50000 : ℝ)+(2113/20000 : ℝ))=(2000267422279603/2000000000000000 : ℝ) by norm_num, show 1+(43338978649660997/100000000000000000000 : ℝ)+(5466753475277713/50000000000000000000 : ℝ)=(100054272485600216423/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43338978649660997/100000000000000000000 : ℝ) ≤ ((5334428988137338229/5336250000000000000 : ℝ)+2*(798307943597/426900000000000 : ℝ)*(7417/50000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (5334428988137338229/5336250000000000000 : ℝ)+2*(798307943597/426900000000000 : ℝ)*(7417/50000 : ℝ)=(2500533854835403/2500000000000000 : ℝ) by norm_num, show 1+2*(43338978649660997/100000000000000000000 : ℝ)=(50043338978649660997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5334428988137338229/5336250000000000000 : ℝ)*(X 1 0+X 2 0)+(798307943597/426900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (7417/50000 : ℝ)) (c := (5334428988137338229/5336250000000000000 : ℝ)) (alpha := (798307943597/426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5334428988137338229/5336250000000000000 : ℝ)*(X 0 1+X 2 1)+(798307943597/426900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (7417/50000 : ℝ)) (c := (5334428988137338229/5336250000000000000 : ℝ)) (alpha := (798307943597/426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5334428988137338229/5336250000000000000 : ℝ)*(X 0 2+X 1 2)+(798307943597/426900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (7417/50000 : ℝ)) (c := (5334428988137338229/5336250000000000000 : ℝ)) (alpha := (798307943597/426900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177063831/10000000000 : ℝ)*X 0 0+(270151141/500000000 : ℝ)*X 0 1+(2628177709/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347235183/10000000000 : ℝ)*X 1 0+(-90064661/400000000 : ℝ)*X 1 1+(1314088881/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167101093/312500000 : ℝ)*X 2 0+(5256355301/10000000000 : ℝ)*X 2 1+(-2251617093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367416637/10000000000 : ℝ)*X 0 0+(4224593883/10000000000 : ℝ)*X 0 1+(4515069939/10000000000 : ℝ)*X 0 2+(4367416637/10000000000 : ℝ)*X 1 0+(4224593883/10000000000 : ℝ)*X 1 1+(4515069939/10000000000 : ℝ)*X 1 2+(4367416637/10000000000 : ℝ)*X 2 0+(4224593883/10000000000 : ℝ)*X 2 1+(4515069939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088535543/5000000000 : ℝ)*X 0 0+(2628388341/5000000000 : ℝ)*X 0 1+(5402599929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331883869/625000000 : ℝ)*X 1 0+(-2105372519/10000000000 : ℝ)*X 1 1+(2701300007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062028397/2000000000 : ℝ)*X 2 0+(675325007/1250000000 : ℝ)*X 2 1+(-32896443/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367431743/10000000000 : ℝ)*X 0 0+(2257117593/5000000000 : ℝ)*X 0 1+(211271583/500000000 : ℝ)*X 0 2+(4367431743/10000000000 : ℝ)*X 1 0+(2257117593/5000000000 : ℝ)*X 1 1+(211271583/500000000 : ℝ)*X 1 2+(4367431743/10000000000 : ℝ)*X 2 0+(2257117593/5000000000 : ℝ)*X 2 1+(211271583/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53218140041548229467468071/17787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (643340109/50000000000000 : ℝ)*(base19) + (119605283/10000000000000 : ℝ)*(base23) + (70882581/50000000000000 : ℝ)*(upper2) + (138945377/50000000000000 : ℝ)*(upper3) + (1026089361125301/20000000000000 : ℝ)*(major0) + (1026089361125301/20000000000000 : ℝ)*(major1) + (1026089361125301/20000000000000 : ℝ)*(major2) + (340909699774841/5000000000000 : ℝ)*(sp0) + (1363644076846243/20000000000000 : ℝ)*(sp1) + (6818207240931423/100000000000000 : ℝ)*(sp2) + (215165438989317/6250000000000 : ℝ)*(sp3) + (27675414613/100000000000000 : ℝ)*(sp4) + (661696359/5000000000000 : ℝ)*(sp6) + (24816783027/100000000000000 : ℝ)*(sp7) + (3442671840612099/100000000000000 : ℝ)*(f.failure) + (6818221670911433/100000000000000 : ℝ)*(f.sum) + (330753559499/711500000000000000000000000 : ℝ)*base65 + (73980951224251857/35575000000000000000000000000000 : ℝ)*base68 + (170675666420173143/35575000000000000000000000000000 : ℝ)*base69 + (9664667027701857/35575000000000000000000000000000 : ℝ)*base72 + (284420848907/142300000000000000000000000 : ℝ)*base73 + (568747521271948143/35575000000000000000000000000000 : ℝ)*base75 + (76467182030573143/35575000000000000000000000000000 : ℝ)*base77 + (95585189591973143/35575000000000000000000000000000 : ℝ)*base79 + (488548975367/355750000000000000000000000 : ℝ)*base82 + (8983587/2500000000000000000000 : ℝ)*base90 + (8983587/2500000000000000000000 : ℝ)*base92 + (8983587/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (463800391784446277808245769/44468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87691471/5000000000000 : ℝ)*(base19) + (1148109389/50000000000000 : ℝ)*(base23) + (329813329/100000000000000 : ℝ)*(upper3) + (33319233/20000000000000 : ℝ)*(lower4) + (147193553/50000000000000 : ℝ)*(upper5) + (5160087781745239/100000000000000 : ℝ)*(major0) + (5160087781745239/100000000000000 : ℝ)*(major1) + (5160087781745239/100000000000000 : ℝ)*(major2) + (36567662819/100000000000000 : ℝ)*(sp1) + (27163498581/50000000000000 : ℝ)*(sp2) + (6857613459645877/100000000000000 : ℝ)*(sp4) + (3428787569076819/50000000000000 : ℝ)*(sp5) + (6857556836429937/100000000000000 : ℝ)*(sp6) + (138502470247377/4000000000000 : ℝ)*(sp7) + (138502470247377/4000000000000 : ℝ)*(f.failure) + (6857613459645877/100000000000000 : ℝ)*(f.sum) + (4864554099949/10672500000000000000000000000 : ℝ)*base65 + (659176544982493077/177875000000000000000000000000000 : ℝ)*base67 + (2699630462709118077/177875000000000000000000000000000 : ℝ)*base69 + (1355345100292493077/177875000000000000000000000000000 : ℝ)*base71 + (58064516193949/10672500000000000000000000000 : ℝ)*base73 + (1709281098313493077/177875000000000000000000000000000 : ℝ)*base75 + (2511152761036993077/177875000000000000000000000000000 : ℝ)*base77 + (439360265862506923/177875000000000000000000000000000 : ℝ)*base80 + (107149539729233/21345000000000000000000000000 : ℝ)*base81 + (490801/100000000000000000000 : ℝ)*base90 + (490801/100000000000000000000 : ℝ)*base92 + (490801/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1119_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7417/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s5_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177750559/10000000000 : ℝ)*x 0 + (2697763973/5000000000 : ℝ)*x 1 + (2631699983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177750559/10000000000 : ℝ)^1039 ≤ (6615176889527/50000000000000 : ℝ)^783 := by
    have hnat : (2177750559 : ℕ)^1039*50000000000000^783 ≤ 6615176889527^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177750559 10000000000 6615176889527 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697763973/5000000000 : ℝ)^1039 ≤ (11024606237077/25000000000000 : ℝ)^783 := by
    have hnat : (2697763973 : ℕ)^1039*25000000000000^783 ≤ 11024606237077^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697763973 5000000000 11024606237077 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631699983/5000000000 : ℝ)^1039 ≤ (2133561063053/5000000000000 : ℝ)^783 := by
    have hnat : (2631699983 : ℕ)^1039*5000000000000^783 ≤ 2133561063053^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631699983 5000000000 2133561063053 5000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177750559/10000000000 : ℝ), (2697763973/5000000000 : ℝ), (2631699983/5000000000 : ℝ)] ![(6615176889527/50000000000000 : ℝ), (11024606237077/25000000000000 : ℝ), (2133561063053/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177750559/10000000000 : ℝ)|^1039 ≤ (6615176889527/50000000000000 : ℝ)^783
        have hw : |(-2177750559/10000000000 : ℝ)|=(2177750559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697763973/5000000000 : ℝ)|^1039 ≤ (11024606237077/25000000000000 : ℝ)^783
        have hw : |(2697763973/5000000000 : ℝ)|=(2697763973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631699983/5000000000 : ℝ)|^1039 ≤ (2133561063053/5000000000000 : ℝ)^783
        have hw : |(2631699983/5000000000 : ℝ)|=(2631699983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267268003/500000000 : ℝ)*x 0 + (-1122402221/5000000000 : ℝ)*x 1 + (1052679993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267268003/500000000 : ℝ)^1039 ≤ (21777583112119/50000000000000 : ℝ)^783 := by
    have hnat : (267268003 : ℕ)^1039*50000000000000^783 ≤ 21777583112119^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267268003 500000000 21777583112119 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122402221/5000000000 : ℝ)^1039 ≤ (13773612509191/100000000000000 : ℝ)^783 := by
    have hnat : (1122402221 : ℕ)^1039*100000000000000^783 ≤ 13773612509191^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122402221 5000000000 13773612509191 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052679993/2000000000 : ℝ)^1039 ≤ (42671221250303/100000000000000 : ℝ)^783 := by
    have hnat : (1052679993 : ℕ)^1039*100000000000000^783 ≤ 42671221250303^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052679993 2000000000 42671221250303 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267268003/500000000 : ℝ), (-1122402221/5000000000 : ℝ), (1052679993/2000000000 : ℝ)] ![(21777583112119/50000000000000 : ℝ), (13773612509191/100000000000000 : ℝ), (42671221250303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267268003/500000000 : ℝ)|^1039 ≤ (21777583112119/50000000000000 : ℝ)^783
        have hw : |(267268003/500000000 : ℝ)|=(267268003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1122402221/5000000000 : ℝ)|^1039 ≤ (13773612509191/100000000000000 : ℝ)^783
        have hw : |(-1122402221/5000000000 : ℝ)|=(1122402221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052679993/2000000000 : ℝ)|^1039 ≤ (42671221250303/100000000000000 : ℝ)^783
        have hw : |(1052679993/2000000000 : ℝ)|=(1052679993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267268003/500000000 : ℝ)*x 0 + (1052679993/2000000000 : ℝ)*x 1 + (-1122402221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267268003/500000000 : ℝ)^1039 ≤ (21777583112119/50000000000000 : ℝ)^783 := by
    have hnat : (267268003 : ℕ)^1039*50000000000000^783 ≤ 21777583112119^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267268003 500000000 21777583112119 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052679993/2000000000 : ℝ)^1039 ≤ (42671221250303/100000000000000 : ℝ)^783 := by
    have hnat : (1052679993 : ℕ)^1039*100000000000000^783 ≤ 42671221250303^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052679993 2000000000 42671221250303 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122402221/5000000000 : ℝ)^1039 ≤ (13773612509191/100000000000000 : ℝ)^783 := by
    have hnat : (1122402221 : ℕ)^1039*100000000000000^783 ≤ 13773612509191^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122402221 5000000000 13773612509191 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267268003/500000000 : ℝ), (1052679993/2000000000 : ℝ), (-1122402221/5000000000 : ℝ)] ![(21777583112119/50000000000000 : ℝ), (42671221250303/100000000000000 : ℝ), (13773612509191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267268003/500000000 : ℝ)|^1039 ≤ (21777583112119/50000000000000 : ℝ)^783
        have hw : |(267268003/500000000 : ℝ)|=(267268003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052679993/2000000000 : ℝ)|^1039 ≤ (42671221250303/100000000000000 : ℝ)^783
        have hw : |(1052679993/2000000000 : ℝ)|=(1052679993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122402221/5000000000 : ℝ)|^1039 ≤ (13773612509191/100000000000000 : ℝ)^783
        have hw : |(-1122402221/5000000000 : ℝ)|=(1122402221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4367819003/10000000000 : ℝ)*x 0 + (2119469779/5000000000 : ℝ)*x 1 + (562577427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367819003/10000000000 : ℝ)^1039 ≤ (33315781513611/100000000000000 : ℝ)^783 := by
    have hnat : (4367819003 : ℕ)^1039*100000000000000^783 ≤ 33315781513611^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367819003 10000000000 33315781513611 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119469779/5000000000 : ℝ)^1039 ≤ (8004419897893/25000000000000 : ℝ)^783 := by
    have hnat : (2119469779 : ℕ)^1039*25000000000000^783 ≤ 8004419897893^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119469779 5000000000 8004419897893 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562577427/1250000000 : ℝ)^1039 ≤ (34666538877857/100000000000000 : ℝ)^783 := by
    have hnat : (562577427 : ℕ)^1039*100000000000000^783 ≤ 34666538877857^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562577427 1250000000 34666538877857 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367819003/10000000000 : ℝ), (2119469779/5000000000 : ℝ), (562577427/1250000000 : ℝ)] ![(33315781513611/100000000000000 : ℝ), (8004419897893/25000000000000 : ℝ), (34666538877857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367819003/10000000000 : ℝ)|^1039 ≤ (33315781513611/100000000000000 : ℝ)^783
        have hw : |(4367819003/10000000000 : ℝ)|=(4367819003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119469779/5000000000 : ℝ)|^1039 ≤ (8004419897893/25000000000000 : ℝ)^783
        have hw : |(2119469779/5000000000 : ℝ)|=(2119469779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562577427/1250000000 : ℝ)|^1039 ≤ (34666538877857/100000000000000 : ℝ)^783
        have hw : |(562577427/1250000000 : ℝ)|=(562577427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177755989/10000000000 : ℝ)*x 0 + (5263742063/10000000000 : ℝ)*x 1 + (5395184567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177755989/10000000000 : ℝ)^1039 ≤ (13230397553143/100000000000000 : ℝ)^783 := by
    have hnat : (2177755989 : ℕ)^1039*100000000000000^783 ≤ 13230397553143^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177755989 10000000000 13230397553143 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263742063/10000000000 : ℝ)^1039 ≤ (8534980300591/20000000000000 : ℝ)^783 := by
    have hnat : (5263742063 : ℕ)^1039*20000000000000^783 ≤ 8534980300591^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263742063 10000000000 8534980300591 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395184567/10000000000 : ℝ)^1039 ≤ (44094700927229/100000000000000 : ℝ)^783 := by
    have hnat : (5395184567 : ℕ)^1039*100000000000000^783 ≤ 44094700927229^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395184567 10000000000 44094700927229 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177755989/10000000000 : ℝ), (5263742063/10000000000 : ℝ), (5395184567/10000000000 : ℝ)] ![(13230397553143/100000000000000 : ℝ), (8534980300591/20000000000000 : ℝ), (44094700927229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177755989/10000000000 : ℝ)|^1039 ≤ (13230397553143/100000000000000 : ℝ)^783
        have hw : |(-2177755989/10000000000 : ℝ)|=(2177755989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263742063/10000000000 : ℝ)|^1039 ≤ (8534980300591/20000000000000 : ℝ)^783
        have hw : |(5263742063/10000000000 : ℝ)|=(5263742063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395184567/10000000000 : ℝ)|^1039 ≤ (44094700927229/100000000000000 : ℝ)^783
        have hw : |(5395184567/10000000000 : ℝ)|=(5395184567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311942881/10000000000 : ℝ)*x 0 + (-528254959/2500000000 : ℝ)*x 1 + (5395184571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311942881/10000000000 : ℝ)^1039 ≤ (1727768830321/4000000000000 : ℝ)^783 := by
    have hnat : (5311942881 : ℕ)^1039*4000000000000^783 ≤ 1727768830321^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311942881 10000000000 1727768830321 4000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528254959/2500000000 : ℝ)^1039 ≤ (12711078259661/100000000000000 : ℝ)^783 := by
    have hnat : (528254959 : ℕ)^1039*100000000000000^783 ≤ 12711078259661^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528254959 2500000000 12711078259661 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395184571/10000000000 : ℝ)^1039 ≤ (44094700970609/100000000000000 : ℝ)^783 := by
    have hnat : (5395184571 : ℕ)^1039*100000000000000^783 ≤ 44094700970609^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395184571 10000000000 44094700970609 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311942881/10000000000 : ℝ), (-528254959/2500000000 : ℝ), (5395184571/10000000000 : ℝ)] ![(1727768830321/4000000000000 : ℝ), (12711078259661/100000000000000 : ℝ), (44094700970609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311942881/10000000000 : ℝ)|^1039 ≤ (1727768830321/4000000000000 : ℝ)^783
        have hw : |(5311942881/10000000000 : ℝ)|=(5311942881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528254959/2500000000 : ℝ)|^1039 ≤ (12711078259661/100000000000000 : ℝ)^783
        have hw : |(-528254959/2500000000 : ℝ)|=(528254959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395184571/10000000000 : ℝ)|^1039 ≤ (44094700970609/100000000000000 : ℝ)^783
        have hw : |(5395184571/10000000000 : ℝ)|=(5395184571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2655971441/5000000000 : ℝ)*x 0 + (674398071/1250000000 : ℝ)*x 1 + (-2113019839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655971441/5000000000 : ℝ)^1039 ≤ (8638844153763/20000000000000 : ℝ)^783 := by
    have hnat : (2655971441 : ℕ)^1039*20000000000000^783 ≤ 8638844153763^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655971441 5000000000 8638844153763 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674398071/1250000000 : ℝ)^1039 ≤ (22047350469037/50000000000000 : ℝ)^783 := by
    have hnat : (674398071 : ℕ)^1039*50000000000000^783 ≤ 22047350469037^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674398071 1250000000 22047350469037 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113019839/10000000000 : ℝ)^1039 ≤ (1588884785451/12500000000000 : ℝ)^783 := by
    have hnat : (2113019839 : ℕ)^1039*12500000000000^783 ≤ 1588884785451^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113019839 10000000000 1588884785451 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655971441/5000000000 : ℝ), (674398071/1250000000 : ℝ), (-2113019839/10000000000 : ℝ)] ![(8638844153763/20000000000000 : ℝ), (22047350469037/50000000000000 : ℝ), (1588884785451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655971441/5000000000 : ℝ)|^1039 ≤ (8638844153763/20000000000000 : ℝ)^783
        have hw : |(2655971441/5000000000 : ℝ)|=(2655971441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674398071/1250000000 : ℝ)|^1039 ≤ (22047350469037/50000000000000 : ℝ)^783
        have hw : |(674398071/1250000000 : ℝ)|=(674398071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113019839/10000000000 : ℝ)|^1039 ≤ (1588884785451/12500000000000 : ℝ)^783
        have hw : |(-2113019839/10000000000 : ℝ)|=(2113019839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s5_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (873565949/2000000000 : ℝ)*x 0 + (2249970937/5000000000 : ℝ)*x 1 + (2119809809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873565949/2000000000 : ℝ)^1039 ≤ (266527121899/800000000000 : ℝ)^783 := by
    have hnat : (873565949 : ℕ)^1039*800000000000^783 ≤ 266527121899^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873565949 2000000000 266527121899 800000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249970937/5000000000 : ℝ)^1039 ≤ (2166225869623/6250000000000 : ℝ)^783 := by
    have hnat : (2249970937 : ℕ)^1039*6250000000000^783 ≤ 2166225869623^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249970937 5000000000 2166225869623 6250000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119809809/5000000000 : ℝ)^1039 ≤ (32024495834123/100000000000000 : ℝ)^783 := by
    have hnat : (2119809809 : ℕ)^1039*100000000000000^783 ≤ 32024495834123^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119809809 5000000000 32024495834123 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873565949/2000000000 : ℝ), (2249970937/5000000000 : ℝ), (2119809809/5000000000 : ℝ)] ![(266527121899/800000000000 : ℝ), (2166225869623/6250000000000 : ℝ), (32024495834123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873565949/2000000000 : ℝ)|^1039 ≤ (266527121899/800000000000 : ℝ)^783
        have hw : |(873565949/2000000000 : ℝ)|=(873565949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249970937/5000000000 : ℝ)|^1039 ≤ (2166225869623/6250000000000 : ℝ)^783
        have hw : |(2249970937/5000000000 : ℝ)|=(2249970937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119809809/5000000000 : ℝ)|^1039 ≤ (32024495834123/100000000000000 : ℝ)^783
        have hw : |(2119809809/5000000000 : ℝ)|=(2119809809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (8311/2048 : ℝ) ≤ (6756241378313541/50000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^8311 ≤ (6756241378313541/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11131 : ℕ)^8311*50000000000000000000^2048 ≤ 6756241378313541^2048*100000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 6756241378313541 50000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (6756241378313541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8311/2048 : ℝ) ≤ (7336905410359281/20000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8311 ≤ (7336905410359281/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8311*20000000000000000000^2048 ≤ 7336905410359281^2048*100000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 7336905410359281 20000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (7336905410359281/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006756241378313541/25000000000000000000 : ℝ) ≤ (10000665882498037/10000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (25006756241378313541/25000000000000000000 : ℝ)^2048 ≤ (10000665882498037/10000000000000000 : ℝ)^8311 := by
      have hnat : (25006756241378313541 : ℕ)^2048*10000000000000000^8311 ≤ 10000665882498037^8311*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006756241378313541 25000000000000000000 10000665882498037 10000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665882498037/10000000000000000 : ℝ)) (X := (25006756241378313541/25000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050197009808423487/100000000000000000000 : ℝ) ≤ (156269323794863/156250000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (100050197009808423487/100000000000000000000 : ℝ)^2048 ≤ (156269323794863/156250000000000 : ℝ)^8311 := by
      have hnat : (100050197009808423487 : ℕ)^2048*156250000000000^8311 ≤ 156269323794863^8311*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050197009808423487 100000000000000000000 156269323794863 156250000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156269323794863/156250000000000 : ℝ)) (X := (100050197009808423487/100000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007336905410359281/10000000000000000000 : ℝ) ≤ (10001807563244427/10000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (10007336905410359281/10000000000000000000 : ℝ)^2048 ≤ (10001807563244427/10000000000000000 : ℝ)^8311 := by
      have hnat : (10007336905410359281 : ℕ)^2048*10000000000000000^8311 ≤ 10001807563244427^8311*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007336905410359281 10000000000000000000 10001807563244427 10000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001807563244427/10000000000000000 : ℝ)) (X := (10007336905410359281/10000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6756241378313541/50000000000000000000 : ℝ) ≤ ((3881170022831354479/3882500000000000000 : ℝ)+2*(114168074639/62120000000000 : ℝ)*(11131/100000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (3881170022831354479/3882500000000000000 : ℝ)+2*(114168074639/62120000000000 : ℝ)*(11131/100000 : ℝ)=(10000665882498037/10000000000000000 : ℝ) by norm_num, show 1+2*(6756241378313541/50000000000000000000 : ℝ)=(25006756241378313541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7336905410359281/20000000000000000000 : ℝ)+(6756241378313541/50000000000000000000 : ℝ) ≤ ((3881170022831354479/3882500000000000000 : ℝ)+(114168074639/62120000000000 : ℝ)*((14237/100000 : ℝ)+(11131/100000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (3881170022831354479/3882500000000000000 : ℝ)+(114168074639/62120000000000 : ℝ)*((14237/100000 : ℝ)+(11131/100000 : ℝ))=(156269323794863/156250000000000 : ℝ) by norm_num, show 1+(7336905410359281/20000000000000000000 : ℝ)+(6756241378313541/50000000000000000000 : ℝ)=(100050197009808423487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7336905410359281/20000000000000000000 : ℝ) ≤ ((3881170022831354479/3882500000000000000 : ℝ)+2*(114168074639/62120000000000 : ℝ)*(14237/100000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (3881170022831354479/3882500000000000000 : ℝ)+2*(114168074639/62120000000000 : ℝ)*(14237/100000 : ℝ)=(10001807563244427/10000000000000000 : ℝ) by norm_num, show 1+2*(7336905410359281/20000000000000000000 : ℝ)=(10007336905410359281/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3881170022831354479/3882500000000000000 : ℝ)*(X 1 0+X 2 0)+(114168074639/62120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3881170022831354479/3882500000000000000 : ℝ)) (alpha := (114168074639/62120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3881170022831354479/3882500000000000000 : ℝ)*(X 0 1+X 2 1)+(114168074639/62120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3881170022831354479/3882500000000000000 : ℝ)) (alpha := (114168074639/62120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3881170022831354479/3882500000000000000 : ℝ)*(X 0 2+X 1 2)+(114168074639/62120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (3881170022831354479/3882500000000000000 : ℝ)) (alpha := (114168074639/62120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177750559/10000000000 : ℝ)*X 0 0+(2697763973/5000000000 : ℝ)*X 0 1+(2631699983/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267268003/500000000 : ℝ)*X 1 0+(-1122402221/5000000000 : ℝ)*X 1 1+(1052679993/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267268003/500000000 : ℝ)*X 2 0+(1052679993/2000000000 : ℝ)*X 2 1+(-1122402221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367819003/10000000000 : ℝ)*X 0 0+(2119469779/5000000000 : ℝ)*X 0 1+(562577427/1250000000 : ℝ)*X 0 2+(4367819003/10000000000 : ℝ)*X 1 0+(2119469779/5000000000 : ℝ)*X 1 1+(562577427/1250000000 : ℝ)*X 1 2+(4367819003/10000000000 : ℝ)*X 2 0+(2119469779/5000000000 : ℝ)*X 2 1+(562577427/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177755989/10000000000 : ℝ)*X 0 0+(5263742063/10000000000 : ℝ)*X 0 1+(5395184567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311942881/10000000000 : ℝ)*X 1 0+(-528254959/2500000000 : ℝ)*X 1 1+(5395184571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655971441/5000000000 : ℝ)*X 2 0+(674398071/1250000000 : ℝ)*X 2 1+(-2113019839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873565949/2000000000 : ℝ)*X 0 0+(2249970937/5000000000 : ℝ)*X 0 1+(2119809809/5000000000 : ℝ)*X 0 2+(873565949/2000000000 : ℝ)*X 1 0+(2249970937/5000000000 : ℝ)*X 1 1+(2119809809/5000000000 : ℝ)*X 1 2+(873565949/2000000000 : ℝ)*X 2 0+(2249970937/5000000000 : ℝ)*X 2 1+(2119809809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18564871575431602709649/3106000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297340181/25000000000000 : ℝ)*(base19) + (1107035999/100000000000000 : ℝ)*(base23) + (44005529/100000000000000 : ℝ)*(lower2) + (151700563/100000000000000 : ℝ)*(upper3) + (45198391/50000000000000 : ℝ)*(upper5) + (5694989764200729/100000000000000 : ℝ)*(major0) + (5694989764200729/100000000000000 : ℝ)*(major1) + (5694989764200729/100000000000000 : ℝ)*(major2) + (1513690470987477/20000000000000 : ℝ)*(sp0) + (7568482344879091/100000000000000 : ℝ)*(sp1) + (946060303400477/12500000000000 : ℝ)*(sp2) + (1910739367613441/50000000000000 : ℝ)*(sp3) + (31179302429/100000000000000 : ℝ)*(sp4) + (17059698099/100000000000000 : ℝ)*(sp7) + (3821495794924981/100000000000000 : ℝ)*(f.failure) + (1513696706847963/20000000000000 : ℝ)*(f.sum) + (6943782981099/3106000000000000000000000000 : ℝ)*base66 + (251557341596902691/388250000000000000000000000000000 : ℝ)*base67 + (2653818868999097309/388250000000000000000000000000000 : ℝ)*base70 + (272611773365402691/388250000000000000000000000000000 : ℝ)*base71 + (1402447754929/3106000000000000000000000000 : ℝ)*base74 + (5989309430270597309/388250000000000000000000000000000 : ℝ)*base76 + (2431737195509597309/388250000000000000000000000000000 : ℝ)*base78 + (4984622162282152691/388250000000000000000000000000000 : ℝ)*base79 + (11324315925099/3106000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10605547/2500000000000000000000 : ℝ)*base89 + (10605547/2500000000000000000000 : ℝ)*base91 + (10605547/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1079809052329632588444153117/97062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2074535763/100000000000000 : ℝ)*(base19) + (28034151/1250000000000 : ℝ)*(base23) + (113299563/50000000000000 : ℝ)*(upper3) + (9589519/12500000000000 : ℝ)*(lower4) + (116961931/50000000000000 : ℝ)*(upper5) + (2862319941229359/50000000000000 : ℝ)*(major0) + (2862319941229359/50000000000000 : ℝ)*(major1) + (2862319941229359/50000000000000 : ℝ)*(major2) + (55524653513/100000000000000 : ℝ)*(sp1) + (7384514563/12500000000000 : ℝ)*(sp2) + (7607887548962121/100000000000000 : ℝ)*(sp4) + (1521565989954569/20000000000000 : ℝ)*(sp5) + (7607826230113537/100000000000000 : ℝ)*(sp6) + (3841391845125843/100000000000000 : ℝ)*(sp7) + (3841391845125843/100000000000000 : ℝ)*(f.failure) + (7607887548962121/100000000000000 : ℝ)*(f.sum) + (4691661412997/1553000000000000000000000000 : ℝ)*base66 + (1449883361025386461/194125000000000000000000000000000 : ℝ)*base67 + (696730934734386461/194125000000000000000000000000000 : ℝ)*base69 + (2294188402826488539/194125000000000000000000000000000 : ℝ)*base72 + (8569274746753/1553000000000000000000000000 : ℝ)*base73 + (2021961173365761461/194125000000000000000000000000000 : ℝ)*base75 + (743841441063613539/194125000000000000000000000000000 : ℝ)*base78 + (887226849974261461/194125000000000000000000000000000 : ℝ)*base79 + (2400363024381/776500000000000000000000000 : ℝ)*base81 + (7924941/2500000000000000000000 : ℝ)*base89 + (7924941/2500000000000000000000 : ℝ)*base91 + (7924941/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1119_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1119_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1119_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1119_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1119_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4143/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1793/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
