-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:34.301222+00:00
-- url     : https://prove2.me/submissions/2dde64e9-bab0-4420-ab4b-44fcc378aae3

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
theorem support_rectangle_w1207_s3_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133034123/10000000000 : ℝ)*x 0 + (2711410951/5000000000 : ℝ)*x 1 + (5237818931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133034123/10000000000 : ℝ)^525 ≤ (3240369488407/25000000000000 : ℝ)^397 := by
    have hnat : (2133034123 : ℕ)^525*25000000000000^397 ≤ 3240369488407^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133034123 10000000000 3240369488407 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711410951/5000000000 : ℝ)^525 ≤ (1391184701191/3125000000000 : ℝ)^397 := by
    have hnat : (2711410951 : ℕ)^525*3125000000000^397 ≤ 1391184701191^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711410951 5000000000 1391184701191 3125000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237818931/10000000000 : ℝ)^525 ≤ (10630152898669/25000000000000 : ℝ)^397 := by
    have hnat : (5237818931 : ℕ)^525*25000000000000^397 ≤ 10630152898669^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237818931 10000000000 10630152898669 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133034123/10000000000 : ℝ), (2711410951/5000000000 : ℝ), (5237818931/10000000000 : ℝ)] ![(3240369488407/25000000000000 : ℝ), (1391184701191/3125000000000 : ℝ), (10630152898669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133034123/10000000000 : ℝ)|^525 ≤ (3240369488407/25000000000000 : ℝ)^397
        have hw : |(-2133034123/10000000000 : ℝ)|=(2133034123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711410951/5000000000 : ℝ)|^525 ≤ (1391184701191/3125000000000 : ℝ)^397
        have hw : |(2711410951/5000000000 : ℝ)|=(2711410951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237818931/10000000000 : ℝ)|^525 ≤ (10630152898669/25000000000000 : ℝ)^397
        have hw : |(5237818931/10000000000 : ℝ)|=(5237818931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5352275219/10000000000 : ℝ)*x 0 + (-445494787/2000000000 : ℝ)*x 1 + (41902553/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352275219/10000000000 : ℝ)^525 ≤ (43753651778803/100000000000000 : ℝ)^397 := by
    have hnat : (5352275219 : ℕ)^525*100000000000000^397 ≤ 43753651778803^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352275219 10000000000 43753651778803 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445494787/2000000000 : ℝ)^525 ≤ (13725734528687/100000000000000 : ℝ)^397 := by
    have hnat : (445494787 : ℕ)^525*100000000000000^397 ≤ 13725734528687^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445494787 2000000000 13725734528687 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41902553/80000000 : ℝ)^525 ≤ (21260306838671/50000000000000 : ℝ)^397 := by
    have hnat : (41902553 : ℕ)^525*50000000000000^397 ≤ 21260306838671^397*80000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41902553 80000000 21260306838671 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352275219/10000000000 : ℝ), (-445494787/2000000000 : ℝ), (41902553/80000000 : ℝ)] ![(43753651778803/100000000000000 : ℝ), (13725734528687/100000000000000 : ℝ), (21260306838671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352275219/10000000000 : ℝ)|^525 ≤ (43753651778803/100000000000000 : ℝ)^397
        have hw : |(5352275219/10000000000 : ℝ)|=(5352275219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445494787/2000000000 : ℝ)|^525 ≤ (13725734528687/100000000000000 : ℝ)^397
        have hw : |(-445494787/2000000000 : ℝ)|=(445494787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41902553/80000000 : ℝ)|^525 ≤ (21260306838671/50000000000000 : ℝ)^397
        have hw : |(41902553/80000000 : ℝ)|=(41902553/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5352275097/10000000000 : ℝ)*x 0 + (1309454853/2500000000 : ℝ)*x 1 + (-2227473719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352275097/10000000000 : ℝ)^525 ≤ (21876825229963/50000000000000 : ℝ)^397 := by
    have hnat : (5352275097 : ℕ)^525*50000000000000^397 ≤ 21876825229963^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352275097 10000000000 21876825229963 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309454853/2500000000 : ℝ)^525 ≤ (42520616758399/100000000000000 : ℝ)^397 := by
    have hnat : (1309454853 : ℕ)^525*100000000000000^397 ≤ 42520616758399^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309454853 2500000000 42520616758399 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227473719/10000000000 : ℝ)^525 ≤ (6862866384277/50000000000000 : ℝ)^397 := by
    have hnat : (2227473719 : ℕ)^525*50000000000000^397 ≤ 6862866384277^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227473719 10000000000 6862866384277 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352275097/10000000000 : ℝ), (1309454853/2500000000 : ℝ), (-2227473719/10000000000 : ℝ)] ![(21876825229963/50000000000000 : ℝ), (42520616758399/100000000000000 : ℝ), (6862866384277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352275097/10000000000 : ℝ)|^525 ≤ (21876825229963/50000000000000 : ℝ)^397
        have hw : |(5352275097/10000000000 : ℝ)|=(5352275097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309454853/2500000000 : ℝ)|^525 ≤ (42520616758399/100000000000000 : ℝ)^397
        have hw : |(1309454853/2500000000 : ℝ)|=(1309454853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227473719/10000000000 : ℝ)|^525 ≤ (6862866384277/50000000000000 : ℝ)^397
        have hw : |(-2227473719/10000000000 : ℝ)|=(2227473719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2176859307/5000000000 : ℝ)*x 0 + (4171246259/10000000000 : ℝ)*x 1 + (1136000617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176859307/5000000000 : ℝ)^525 ≤ (8324581215051/25000000000000 : ℝ)^397 := by
    have hnat : (2176859307 : ℕ)^525*25000000000000^397 ≤ 8324581215051^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176859307 5000000000 8324581215051 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171246259/10000000000 : ℝ)^525 ≤ (15732677898937/50000000000000 : ℝ)^397 := by
    have hnat : (4171246259 : ℕ)^525*50000000000000^397 ≤ 15732677898937^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171246259 10000000000 15732677898937 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136000617/2500000000 : ℝ)^525 ≤ (220226995829/625000000000 : ℝ)^397 := by
    have hnat : (1136000617 : ℕ)^525*625000000000^397 ≤ 220226995829^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136000617 2500000000 220226995829 625000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176859307/5000000000 : ℝ), (4171246259/10000000000 : ℝ), (1136000617/2500000000 : ℝ)] ![(8324581215051/25000000000000 : ℝ), (15732677898937/50000000000000 : ℝ), (220226995829/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176859307/5000000000 : ℝ)|^525 ≤ (8324581215051/25000000000000 : ℝ)^397
        have hw : |(2176859307/5000000000 : ℝ)|=(2176859307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171246259/10000000000 : ℝ)|^525 ≤ (15732677898937/50000000000000 : ℝ)^397
        have hw : |(4171246259/10000000000 : ℝ)|=(4171246259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136000617/2500000000 : ℝ)|^525 ≤ (220226995829/625000000000 : ℝ)^397
        have hw : |(1136000617/2500000000 : ℝ)|=(1136000617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066524729/5000000000 : ℝ)*x 0 + (2619253121/5000000000 : ℝ)*x 1 + (5422130861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066524729/5000000000 : ℝ)^525 ≤ (12961601181743/100000000000000 : ℝ)^397 := by
    have hnat : (1066524729 : ℕ)^525*100000000000000^397 ≤ 12961601181743^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066524729 5000000000 12961601181743 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619253121/5000000000 : ℝ)^525 ≤ (42527990302257/100000000000000 : ℝ)^397 := by
    have hnat : (2619253121 : ℕ)^525*100000000000000^397 ≤ 42527990302257^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619253121 5000000000 42527990302257 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422130861/10000000000 : ℝ)^525 ≤ (22255204253087/50000000000000 : ℝ)^397 := by
    have hnat : (5422130861 : ℕ)^525*50000000000000^397 ≤ 22255204253087^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422130861 10000000000 22255204253087 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066524729/5000000000 : ℝ), (2619253121/5000000000 : ℝ), (5422130861/10000000000 : ℝ)] ![(12961601181743/100000000000000 : ℝ), (42527990302257/100000000000000 : ℝ), (22255204253087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066524729/5000000000 : ℝ)|^525 ≤ (12961601181743/100000000000000 : ℝ)^397
        have hw : |(-1066524729/5000000000 : ℝ)|=(1066524729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619253121/5000000000 : ℝ)|^525 ≤ (42527990302257/100000000000000 : ℝ)^397
        have hw : |(2619253121/5000000000 : ℝ)|=(2619253121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422130861/10000000000 : ℝ)|^525 ≤ (22255204253087/50000000000000 : ℝ)^397
        have hw : |(5422130861/10000000000 : ℝ)|=(5422130861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305188969/10000000000 : ℝ)*x 0 + (-1021581127/5000000000 : ℝ)*x 1 + (338883159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305188969/10000000000 : ℝ)^525 ≤ (21622675265929/50000000000000 : ℝ)^397 := by
    have hnat : (5305188969 : ℕ)^525*50000000000000^397 ≤ 21622675265929^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305188969 10000000000 21622675265929 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021581127/5000000000 : ℝ)^525 ≤ (2448848877987/20000000000000 : ℝ)^397 := by
    have hnat : (1021581127 : ℕ)^525*20000000000000^397 ≤ 2448848877987^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021581127 5000000000 2448848877987 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338883159/625000000 : ℝ)^525 ≤ (44510405064897/100000000000000 : ℝ)^397 := by
    have hnat : (338883159 : ℕ)^525*100000000000000^397 ≤ 44510405064897^397*625000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338883159 625000000 44510405064897 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305188969/10000000000 : ℝ), (-1021581127/5000000000 : ℝ), (338883159/625000000 : ℝ)] ![(21622675265929/50000000000000 : ℝ), (2448848877987/20000000000000 : ℝ), (44510405064897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305188969/10000000000 : ℝ)|^525 ≤ (21622675265929/50000000000000 : ℝ)^397
        have hw : |(5305188969/10000000000 : ℝ)|=(5305188969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021581127/5000000000 : ℝ)|^525 ≤ (2448848877987/20000000000000 : ℝ)^397
        have hw : |(-1021581127/5000000000 : ℝ)|=(1021581127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338883159/625000000 : ℝ)|^525 ≤ (44510405064897/100000000000000 : ℝ)^397
        have hw : |(338883159/625000000 : ℝ)|=(338883159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652594421/5000000000 : ℝ)*x 0 + (2711065267/5000000000 : ℝ)*x 1 + (-2043162441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652594421/5000000000 : ℝ)^525 ≤ (21622674581417/50000000000000 : ℝ)^397 := by
    have hnat : (2652594421 : ℕ)^525*50000000000000^397 ≤ 21622674581417^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652594421 5000000000 21622674581417 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711065267/5000000000 : ℝ)^525 ≤ (44510404956339/100000000000000 : ℝ)^397 := by
    have hnat : (2711065267 : ℕ)^525*100000000000000^397 ≤ 44510404956339^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711065267 5000000000 44510404956339 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043162441/10000000000 : ℝ)^525 ≤ (2448849174381/20000000000000 : ℝ)^397 := by
    have hnat : (2043162441 : ℕ)^525*20000000000000^397 ≤ 2448849174381^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043162441 10000000000 2448849174381 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652594421/5000000000 : ℝ), (2711065267/5000000000 : ℝ), (-2043162441/10000000000 : ℝ)] ![(21622674581417/50000000000000 : ℝ), (44510404956339/100000000000000 : ℝ), (2448849174381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652594421/5000000000 : ℝ)|^525 ≤ (21622674581417/50000000000000 : ℝ)^397
        have hw : |(2652594421/5000000000 : ℝ)|=(2652594421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711065267/5000000000 : ℝ)|^525 ≤ (44510404956339/100000000000000 : ℝ)^397
        have hw : |(2711065267/5000000000 : ℝ)|=(2711065267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043162441/10000000000 : ℝ)|^525 ≤ (2448849174381/20000000000000 : ℝ)^397
        have hw : |(-2043162441/10000000000 : ℝ)|=(2043162441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s3_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (108843741/250000000 : ℝ)*x 0 + (4542617233/10000000000 : ℝ)*x 1 + (1043159663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108843741/250000000 : ℝ)^525 ≤ (33298638663219/100000000000000 : ℝ)^397 := by
    have hnat : (108843741 : ℕ)^525*100000000000000^397 ≤ 33298638663219^397*250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108843741 250000000 33298638663219 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542617233/10000000000 : ℝ)^525 ≤ (7044422986577/20000000000000 : ℝ)^397 := by
    have hnat : (4542617233 : ℕ)^525*20000000000000^397 ≤ 7044422986577^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542617233 10000000000 7044422986577 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043159663/2500000000 : ℝ)^525 ≤ (31479246391719/100000000000000 : ℝ)^397 := by
    have hnat : (1043159663 : ℕ)^525*100000000000000^397 ≤ 31479246391719^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043159663 2500000000 31479246391719 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108843741/250000000 : ℝ), (4542617233/10000000000 : ℝ), (1043159663/2500000000 : ℝ)] ![(33298638663219/100000000000000 : ℝ), (7044422986577/20000000000000 : ℝ), (31479246391719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108843741/250000000 : ℝ)|^525 ≤ (33298638663219/100000000000000 : ℝ)^397
        have hw : |(108843741/250000000 : ℝ)|=(108843741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542617233/10000000000 : ℝ)|^525 ≤ (7044422986577/20000000000000 : ℝ)^397
        have hw : |(4542617233/10000000000 : ℝ)|=(4542617233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043159663/2500000000 : ℝ)|^525 ≤ (31479246391719/100000000000000 : ℝ)^397
        have hw : |(1043159663/2500000000 : ℝ)|=(1043159663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10819/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4677/50000 : ℝ) ^ (8399/2048 : ℝ) ≤ (6025371444677631/100000000000000000000 : ℝ) := by
    have hpowers : (4677/50000 : ℝ)^8399 ≤ (6025371444677631/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4677 : ℕ)^8399*100000000000000000000^2048 ≤ 6025371444677631^2048*50000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4677 50000 6025371444677631 100000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4677/50000 : ℝ)) (X := (6025371444677631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16317/100000 : ℝ) ^ (8399/2048 : ℝ) ≤ (14754330164030977/25000000000000000000 : ℝ) := by
    have hpowers : (16317/100000 : ℝ)^8399 ≤ (14754330164030977/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16317 : ℕ)^8399*25000000000000000000^2048 ≤ 14754330164030977^2048*100000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16317 100000 14754330164030977 25000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16317/100000 : ℝ)) (X := (14754330164030977/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006025371444677631/50000000000000000000 : ℝ) ≤ (5000146915091449/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (50006025371444677631/50000000000000000000 : ℝ)^2048 ≤ (5000146915091449/5000000000000000 : ℝ)^8399 := by
      have hnat : (50006025371444677631 : ℕ)^2048*5000000000000000^8399 ≤ 5000146915091449^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006025371444677631 50000000000000000000 5000146915091449 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000146915091449/5000000000000000 : ℝ)) (X := (50006025371444677631/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100065042692100801539/100000000000000000000 : ℝ) ≤ (625099100107403/625000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (100065042692100801539/100000000000000000000 : ℝ)^2048 ≤ (625099100107403/625000000000000 : ℝ)^8399 := by
      have hnat : (100065042692100801539 : ℕ)^2048*625000000000000^8399 ≤ 625099100107403^8399*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065042692100801539 100000000000000000000 625099100107403 625000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625099100107403/625000000000000 : ℝ)) (X := (100065042692100801539/100000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514754330164030977/12500000000000000000 : ℝ) ≤ (5001438686626999/5000000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (12514754330164030977/12500000000000000000 : ℝ)^2048 ≤ (5001438686626999/5000000000000000 : ℝ)^8399 := by
      have hnat : (12514754330164030977 : ℕ)^2048*5000000000000000^8399 ≤ 5001438686626999^8399*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514754330164030977 12500000000000000000 5001438686626999 5000000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001438686626999/5000000000000000 : ℝ)) (X := (12514754330164030977/12500000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6025371444677631/100000000000000000000 : ℝ) ≤ ((11601313246279408229/11605000000000000000 : ℝ)+2*(8611810237/4642000000000 : ℝ)*(4677/50000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (11601313246279408229/11605000000000000000 : ℝ)+2*(8611810237/4642000000000 : ℝ)*(4677/50000 : ℝ)=(5000146915091449/5000000000000000 : ℝ) by norm_num, show 1+2*(6025371444677631/100000000000000000000 : ℝ)=(50006025371444677631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14754330164030977/25000000000000000000 : ℝ)+(6025371444677631/100000000000000000000 : ℝ) ≤ ((11601313246279408229/11605000000000000000 : ℝ)+(8611810237/4642000000000 : ℝ)*((16317/100000 : ℝ)+(4677/50000 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (11601313246279408229/11605000000000000000 : ℝ)+(8611810237/4642000000000 : ℝ)*((16317/100000 : ℝ)+(4677/50000 : ℝ))=(625099100107403/625000000000000 : ℝ) by norm_num, show 1+(14754330164030977/25000000000000000000 : ℝ)+(6025371444677631/100000000000000000000 : ℝ)=(100065042692100801539/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14754330164030977/25000000000000000000 : ℝ) ≤ ((11601313246279408229/11605000000000000000 : ℝ)+2*(8611810237/4642000000000 : ℝ)*(16317/100000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (11601313246279408229/11605000000000000000 : ℝ)+2*(8611810237/4642000000000 : ℝ)*(16317/100000 : ℝ)=(5001438686626999/5000000000000000 : ℝ) by norm_num, show 1+2*(14754330164030977/25000000000000000000 : ℝ)=(12514754330164030977/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11601313246279408229/11605000000000000000 : ℝ)*(X 1 0+X 2 0)+(8611810237/4642000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (11601313246279408229/11605000000000000000 : ℝ)) (alpha := (8611810237/4642000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11601313246279408229/11605000000000000000 : ℝ)*(X 0 1+X 2 1)+(8611810237/4642000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (11601313246279408229/11605000000000000000 : ℝ)) (alpha := (8611810237/4642000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11601313246279408229/11605000000000000000 : ℝ)*(X 0 2+X 1 2)+(8611810237/4642000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (4677/50000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (11601313246279408229/11605000000000000000 : ℝ)) (alpha := (8611810237/4642000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133034123/10000000000 : ℝ)*X 0 0+(2711410951/5000000000 : ℝ)*X 0 1+(5237818931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352275219/10000000000 : ℝ)*X 1 0+(-445494787/2000000000 : ℝ)*X 1 1+(41902553/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352275097/10000000000 : ℝ)*X 2 0+(1309454853/2500000000 : ℝ)*X 2 1+(-2227473719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176859307/5000000000 : ℝ)*X 0 0+(4171246259/10000000000 : ℝ)*X 0 1+(1136000617/2500000000 : ℝ)*X 0 2+(2176859307/5000000000 : ℝ)*X 1 0+(4171246259/10000000000 : ℝ)*X 1 1+(1136000617/2500000000 : ℝ)*X 1 2+(2176859307/5000000000 : ℝ)*X 2 0+(4171246259/10000000000 : ℝ)*X 2 1+(1136000617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1066524729/5000000000 : ℝ)*X 0 0+(2619253121/5000000000 : ℝ)*X 0 1+(5422130861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305188969/10000000000 : ℝ)*X 1 0+(-1021581127/5000000000 : ℝ)*X 1 1+(338883159/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652594421/5000000000 : ℝ)*X 2 0+(2711065267/5000000000 : ℝ)*X 2 1+(-2043162441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108843741/250000000 : ℝ)*X 0 0+(4542617233/10000000000 : ℝ)*X 0 1+(1043159663/2500000000 : ℝ)*X 0 2+(108843741/250000000 : ℝ)*X 1 0+(4542617233/10000000000 : ℝ)*X 1 1+(1043159663/2500000000 : ℝ)*X 1 2+(108843741/250000000 : ℝ)*X 2 0+(4542617233/10000000000 : ℝ)*X 2 1+(1043159663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (980936415594548232793385019/145062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (938960191/100000000000000 : ℝ)*(base19) + (643720441/100000000000000 : ℝ)*(base23) + (92074929/100000000000000 : ℝ)*(lower2) + (35292787/100000000000000 : ℝ)*(upper3) + (12388951/10000000000000 : ℝ)*(upper5) + (2022027417893163/50000000000000 : ℝ)*(major0) + (2022027417893163/50000000000000 : ℝ)*(major1) + (2022027417893163/50000000000000 : ℝ)*(major2) + (1081068484389043/20000000000000 : ℝ)*(sp0) + (1351342379533273/25000000000000 : ℝ)*(sp1) + (5405369813372843/100000000000000 : ℝ)*(sp2) + (1341364621157119/50000000000000 : ℝ)*(sp3) + (28035148069/100000000000000 : ℝ)*(sp4) + (9746759649/100000000000000 : ℝ)*(sp7) + (83835593408559/3125000000000 : ℝ)*(f.failure) + (1351342614273321/25000000000000 : ℝ)*(f.sum) + (904438477831/92840000000000000000000000 : ℝ)*base65 + (1983327123080788327/580250000000000000000000000000000 : ℝ)*base67 + (11060002278406038327/580250000000000000000000000000000 : ℝ)*base69 + (8121422165052538327/580250000000000000000000000000000 : ℝ)*base71 + (2490037956301/2321000000000000000000000000 : ℝ)*base73 + (5854195445844538327/580250000000000000000000000000000 : ℝ)*base75 + (10610959477806788327/580250000000000000000000000000000 : ℝ)*base77 + (5015754381631211673/580250000000000000000000000000000 : ℝ)*base80 + (3645901174081/464200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1273587/312500000000000000000 : ℝ)*base90 + (1273587/312500000000000000000 : ℝ)*base92 + (1273587/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43463364041880394013596371/18132812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (643133919/100000000000000 : ℝ)*(base19) + (162220197/25000000000000 : ℝ)*(base23) + (9597743/10000000000000 : ℝ)*(lower4) + (43973661/50000000000000 : ℝ)*(upper5) + (254648800386633/6250000000000 : ℝ)*(major0) + (254648800386633/6250000000000 : ℝ)*(major1) + (254648800386633/6250000000000 : ℝ)*(major2) + (1217293863/20000000000000 : ℝ)*(sp0) + (6346975603/50000000000000 : ℝ)*(sp1) + (3823348561/50000000000000 : ℝ)*(sp2) + (1361474715122377/25000000000000 : ℝ)*(sp4) + (5445891609873699/100000000000000 : ℝ)*(sp5) + (340368540711307/6250000000000 : ℝ)*(sp6) + (2702856585515241/100000000000000 : ℝ)*(sp7) + (2702856585515241/100000000000000 : ℝ)*(f.failure) + (5445904946958823/100000000000000 : ℝ)*(f.sum) + (1727237545391/2321000000000000000000000000 : ℝ)*base66 + (374292491502540793/72531250000000000000000000000000 : ℝ)*base68 + (561438316586478293/72531250000000000000000000000000 : ℝ)*base70 + (823120179645853293/72531250000000000000000000000000 : ℝ)*base72 + (9486419844677/2321000000000000000000000000 : ℝ)*base74 + (1140431230565009543/72531250000000000000000000000000 : ℝ)*base76 + (37871866477490457/72531250000000000000000000000000 : ℝ)*base77 + (189312650600228293/72531250000000000000000000000000 : ℝ)*base80 + (2911078931951/1160500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (30290187/10000000000000000000000 : ℝ)*base89 + (30290187/10000000000000000000000 : ℝ)*base91 + (30290187/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1207_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10819/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1207_s4_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135555737/10000000000 : ℝ)*x 0 + (107978933/200000000 : ℝ)*x 1 + (5260042687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135555737/10000000000 : ℝ)^525 ≤ (12981744832067/100000000000000 : ℝ)^397 := by
    have hnat : (2135555737 : ℕ)^525*100000000000000^397 ≤ 12981744832067^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135555737 10000000000 12981744832067 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107978933/200000000 : ℝ)^525 ≤ (8851779968709/20000000000000 : ℝ)^397 := by
    have hnat : (107978933 : ℕ)^525*20000000000000^397 ≤ 8851779968709^397*200000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107978933 200000000 8851779968709 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260042687/10000000000 : ℝ)^525 ≤ (4275935531137/10000000000000 : ℝ)^397 := by
    have hnat : (5260042687 : ℕ)^525*10000000000000^397 ≤ 4275935531137^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260042687 10000000000 4275935531137 10000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135555737/10000000000 : ℝ), (107978933/200000000 : ℝ), (5260042687/10000000000 : ℝ)] ![(12981744832067/100000000000000 : ℝ), (8851779968709/20000000000000 : ℝ), (4275935531137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135555737/10000000000 : ℝ)|^525 ≤ (12981744832067/100000000000000 : ℝ)^397
        have hw : |(-2135555737/10000000000 : ℝ)|=(2135555737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107978933/200000000 : ℝ)|^525 ≤ (8851779968709/20000000000000 : ℝ)^397
        have hw : |(107978933/200000000 : ℝ)|=(107978933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260042687/10000000000 : ℝ)|^525 ≤ (4275935531137/10000000000000 : ℝ)^397
        have hw : |(5260042687/10000000000 : ℝ)|=(5260042687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1069255079/2000000000 : ℝ)*x 0 + (-1103050549/5000000000 : ℝ)*x 1 + (5260042669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069255079/2000000000 : ℝ)^525 ≤ (8737760514449/20000000000000 : ℝ)^397 := by
    have hnat : (1069255079 : ℕ)^525*20000000000000^397 ≤ 8737760514449^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069255079 2000000000 8737760514449 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103050549/5000000000 : ℝ)^525 ≤ (13551842299031/100000000000000 : ℝ)^397 := by
    have hnat : (1103050549 : ℕ)^525*100000000000000^397 ≤ 13551842299031^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103050549 5000000000 13551842299031 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260042669/10000000000 : ℝ)^525 ≤ (42759355117869/100000000000000 : ℝ)^397 := by
    have hnat : (5260042669 : ℕ)^525*100000000000000^397 ≤ 42759355117869^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260042669 10000000000 42759355117869 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069255079/2000000000 : ℝ), (-1103050549/5000000000 : ℝ), (5260042669/10000000000 : ℝ)] ![(8737760514449/20000000000000 : ℝ), (13551842299031/100000000000000 : ℝ), (42759355117869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069255079/2000000000 : ℝ)|^525 ≤ (8737760514449/20000000000000 : ℝ)^397
        have hw : |(1069255079/2000000000 : ℝ)|=(1069255079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103050549/5000000000 : ℝ)|^525 ≤ (13551842299031/100000000000000 : ℝ)^397
        have hw : |(-1103050549/5000000000 : ℝ)|=(1103050549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260042669/10000000000 : ℝ)|^525 ≤ (42759355117869/100000000000000 : ℝ)^397
        have hw : |(5260042669/10000000000 : ℝ)|=(5260042669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42770203/80000000 : ℝ)*x 0 + (2630021349/5000000000 : ℝ)*x 1 + (-1103050543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42770203/80000000 : ℝ)^525 ≤ (21844401178057/50000000000000 : ℝ)^397 := by
    have hnat : (42770203 : ℕ)^525*50000000000000^397 ≤ 21844401178057^397*80000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42770203 80000000 21844401178057 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630021349/5000000000 : ℝ)^525 ≤ (42759355429621/100000000000000 : ℝ)^397 := by
    have hnat : (2630021349 : ℕ)^525*100000000000000^397 ≤ 42759355429621^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630021349 5000000000 42759355429621 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103050543/5000000000 : ℝ)^525 ≤ (13551842201549/100000000000000 : ℝ)^397 := by
    have hnat : (1103050543 : ℕ)^525*100000000000000^397 ≤ 13551842201549^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103050543 5000000000 13551842201549 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42770203/80000000 : ℝ), (2630021349/5000000000 : ℝ), (-1103050543/5000000000 : ℝ)] ![(21844401178057/50000000000000 : ℝ), (42759355429621/100000000000000 : ℝ), (13551842201549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42770203/80000000 : ℝ)|^525 ≤ (21844401178057/50000000000000 : ℝ)^397
        have hw : |(42770203/80000000 : ℝ)|=(42770203/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630021349/5000000000 : ℝ)|^525 ≤ (42759355429621/100000000000000 : ℝ)^397
        have hw : |(2630021349/5000000000 : ℝ)|=(2630021349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103050543/5000000000 : ℝ)|^525 ≤ (13551842201549/100000000000000 : ℝ)^397
        have hw : |(-1103050543/5000000000 : ℝ)|=(1103050543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4355227799/10000000000 : ℝ)*x 0 + (4217494013/10000000000 : ℝ)*x 1 + (4497367411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355227799/10000000000 : ℝ)^525 ≤ (33313589887059/100000000000000 : ℝ)^397 := by
    have hnat : (4355227799 : ℕ)^525*100000000000000^397 ≤ 33313589887059^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355227799 10000000000 33313589887059 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217494013/10000000000 : ℝ)^525 ≤ (1596376190313/5000000000000 : ℝ)^397 := by
    have hnat : (4217494013 : ℕ)^525*5000000000000^397 ≤ 1596376190313^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217494013 10000000000 1596376190313 5000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497367411/10000000000 : ℝ)^525 ≤ (17379443140007/50000000000000 : ℝ)^397 := by
    have hnat : (4497367411 : ℕ)^525*50000000000000^397 ≤ 17379443140007^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497367411 10000000000 17379443140007 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355227799/10000000000 : ℝ), (4217494013/10000000000 : ℝ), (4497367411/10000000000 : ℝ)] ![(33313589887059/100000000000000 : ℝ), (1596376190313/5000000000000 : ℝ), (17379443140007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355227799/10000000000 : ℝ)|^525 ≤ (33313589887059/100000000000000 : ℝ)^397
        have hw : |(4355227799/10000000000 : ℝ)|=(4355227799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217494013/10000000000 : ℝ)|^525 ≤ (1596376190313/5000000000000 : ℝ)^397
        have hw : |(4217494013/10000000000 : ℝ)|=(4217494013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497367411/10000000000 : ℝ)|^525 ≤ (17379443140007/50000000000000 : ℝ)^397
        have hw : |(4497367411/10000000000 : ℝ)|=(4497367411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135562359/10000000000 : ℝ)*x 0 + (5260430839/10000000000 : ℝ)*x 1 + (2699278413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135562359/10000000000 : ℝ)^525 ≤ (6490899032497/50000000000000 : ℝ)^397 := by
    have hnat : (2135562359 : ℕ)^525*50000000000000^397 ≤ 6490899032497^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135562359 10000000000 6490899032497 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260430839/10000000000 : ℝ)^525 ≤ (8552705603253/20000000000000 : ℝ)^397 := by
    have hnat : (5260430839 : ℕ)^525*20000000000000^397 ≤ 8552705603253^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260430839 10000000000 8552705603253 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699278413/5000000000 : ℝ)^525 ≤ (2765917118627/6250000000000 : ℝ)^397 := by
    have hnat : (2699278413 : ℕ)^525*6250000000000^397 ≤ 2765917118627^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699278413 5000000000 2765917118627 6250000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135562359/10000000000 : ℝ), (5260430839/10000000000 : ℝ), (2699278413/5000000000 : ℝ)] ![(6490899032497/50000000000000 : ℝ), (8552705603253/20000000000000 : ℝ), (2765917118627/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135562359/10000000000 : ℝ)|^525 ≤ (6490899032497/50000000000000 : ℝ)^397
        have hw : |(-2135562359/10000000000 : ℝ)|=(2135562359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260430839/10000000000 : ℝ)|^525 ≤ (8552705603253/20000000000000 : ℝ)^397
        have hw : |(5260430839/10000000000 : ℝ)|=(5260430839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699278413/5000000000 : ℝ)|^525 ≤ (2765917118627/6250000000000 : ℝ)^397
        have hw : |(2699278413/5000000000 : ℝ)|=(2699278413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1327730093/2500000000 : ℝ)*x 0 + (-516896737/2500000000 : ℝ)*x 1 + (5398556861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327730093/2500000000 : ℝ)^525 ≤ (43307144191859/100000000000000 : ℝ)^397 := by
    have hnat : (1327730093 : ℕ)^525*100000000000000^397 ≤ 43307144191859^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327730093 2500000000 43307144191859 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516896737/2500000000 : ℝ)^525 ≤ (12438181518939/100000000000000 : ℝ)^397 := by
    have hnat : (516896737 : ℕ)^525*100000000000000^397 ≤ 12438181518939^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516896737 2500000000 12438181518939 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398556861/10000000000 : ℝ)^525 ≤ (885093485549/2000000000000 : ℝ)^397 := by
    have hnat : (5398556861 : ℕ)^525*2000000000000^397 ≤ 885093485549^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398556861 10000000000 885093485549 2000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327730093/2500000000 : ℝ), (-516896737/2500000000 : ℝ), (5398556861/10000000000 : ℝ)] ![(43307144191859/100000000000000 : ℝ), (12438181518939/100000000000000 : ℝ), (885093485549/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327730093/2500000000 : ℝ)|^525 ≤ (43307144191859/100000000000000 : ℝ)^397
        have hw : |(1327730093/2500000000 : ℝ)|=(1327730093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516896737/2500000000 : ℝ)|^525 ≤ (12438181518939/100000000000000 : ℝ)^397
        have hw : |(-516896737/2500000000 : ℝ)|=(516896737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398556861/10000000000 : ℝ)|^525 ≤ (885093485549/2000000000000 : ℝ)^397
        have hw : |(5398556861/10000000000 : ℝ)|=(5398556861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1062184059/2000000000 : ℝ)*x 0 + (539855697/1000000000 : ℝ)*x 1 + (-258448363/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062184059/2000000000 : ℝ)^525 ≤ (10826785840383/25000000000000 : ℝ)^397 := by
    have hnat : (1062184059 : ℕ)^525*25000000000000^397 ≤ 10826785840383^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062184059 2000000000 10826785840383 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539855697/1000000000 : ℝ)^525 ≤ (44254675459067/100000000000000 : ℝ)^397 := by
    have hnat : (539855697 : ℕ)^525*100000000000000^397 ≤ 44254675459067^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539855697 1000000000 44254675459067 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258448363/1250000000 : ℝ)^525 ≤ (12438181168901/100000000000000 : ℝ)^397 := by
    have hnat : (258448363 : ℕ)^525*100000000000000^397 ≤ 12438181168901^397*1250000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258448363 1250000000 12438181168901 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062184059/2000000000 : ℝ), (539855697/1000000000 : ℝ), (-258448363/1250000000 : ℝ)] ![(10826785840383/25000000000000 : ℝ), (44254675459067/100000000000000 : ℝ), (12438181168901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062184059/2000000000 : ℝ)|^525 ≤ (10826785840383/25000000000000 : ℝ)^397
        have hw : |(1062184059/2000000000 : ℝ)|=(1062184059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539855697/1000000000 : ℝ)|^525 ≤ (44254675459067/100000000000000 : ℝ)^397
        have hw : |(539855697/1000000000 : ℝ)|=(539855697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258448363/1250000000 : ℝ)|^525 ≤ (12438181168901/100000000000000 : ℝ)^397
        have hw : |(-258448363/1250000000 : ℝ)|=(258448363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s4_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2177620443/5000000000 : ℝ)*x 0 + (1124146347/2500000000 : ℝ)*x 1 + (4218279137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177620443/5000000000 : ℝ)^525 ≤ (33313722266233/100000000000000 : ℝ)^397 := by
    have hnat : (2177620443 : ℕ)^525*100000000000000^397 ≤ 33313722266233^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177620443 5000000000 33313722266233 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124146347/2500000000 : ℝ)^525 ≤ (8687723440461/25000000000000 : ℝ)^397 := by
    have hnat : (1124146347 : ℕ)^525*25000000000000^397 ≤ 8687723440461^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124146347 2500000000 8687723440461 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218279137/10000000000 : ℝ)^525 ≤ (15967691978231/50000000000000 : ℝ)^397 := by
    have hnat : (4218279137 : ℕ)^525*50000000000000^397 ≤ 15967691978231^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218279137 10000000000 15967691978231 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177620443/5000000000 : ℝ), (1124146347/2500000000 : ℝ), (4218279137/10000000000 : ℝ)] ![(33313722266233/100000000000000 : ℝ), (8687723440461/25000000000000 : ℝ), (15967691978231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177620443/5000000000 : ℝ)|^525 ≤ (33313722266233/100000000000000 : ℝ)^397
        have hw : |(2177620443/5000000000 : ℝ)|=(2177620443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124146347/2500000000 : ℝ)|^525 ≤ (8687723440461/25000000000000 : ℝ)^397
        have hw : |(1124146347/2500000000 : ℝ)|=(1124146347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218279137/10000000000 : ℝ)|^525 ≤ (15967691978231/50000000000000 : ℝ)^397
        have hw : |(4218279137/10000000000 : ℝ)|=(4218279137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10819/100000 : ℝ) ^ (8399/2048 : ℝ) ≤ (10942831223658663/100000000000000000000 : ℝ) := by
    have hpowers : (10819/100000 : ℝ)^8399 ≤ (10942831223658663/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10819 : ℕ)^8399*100000000000000000000^2048 ≤ 10942831223658663^2048*100000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10819 100000 10942831223658663 100000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10819/100000 : ℝ)) (X := (10942831223658663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7367/50000 : ℝ) ^ (8399/2048 : ℝ) ≤ (9708705593724713/25000000000000000000 : ℝ) := by
    have hpowers : (7367/50000 : ℝ)^8399 ≤ (9708705593724713/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7367 : ℕ)^8399*25000000000000000000^2048 ≤ 9708705593724713^2048*50000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7367 50000 9708705593724713 25000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7367/50000 : ℝ)) (X := (9708705593724713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010942831223658663/50000000000000000000 : ℝ) ≤ (4000213445069/4000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (50010942831223658663/50000000000000000000 : ℝ)^2048 ≤ (4000213445069/4000000000000 : ℝ)^8399 := by
      have hnat : (50010942831223658663 : ℕ)^2048*4000000000000^8399 ≤ 4000213445069^8399*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010942831223658663 50000000000000000000 4000213445069 4000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4000213445069/4000000000000 : ℝ)) (X := (50010942831223658663/50000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009955530719711503/20000000000000000000 : ℝ) ≤ (8000970834187/8000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (20009955530719711503/20000000000000000000 : ℝ)^2048 ≤ (8000970834187/8000000000000 : ℝ)^8399 := by
      have hnat : (20009955530719711503 : ℕ)^2048*8000000000000^8399 ≤ 8000970834187^8399*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009955530719711503 20000000000000000000 8000970834187 8000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8000970834187/8000000000000 : ℝ)) (X := (20009955530719711503/20000000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509708705593724713/12500000000000000000 : ℝ) ≤ (2000378694559/2000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (12509708705593724713/12500000000000000000 : ℝ)^2048 ≤ (2000378694559/2000000000000 : ℝ)^8399 := by
      have hnat : (12509708705593724713 : ℕ)^2048*2000000000000^8399 ≤ 2000378694559^8399*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509708705593724713 12500000000000000000 2000378694559 2000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000378694559/2000000000000 : ℝ)) (X := (12509708705593724713/12500000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10942831223658663/100000000000000000000 : ℝ) ≤ ((1304579225564917/1305000000000000 : ℝ)+2*(181314683/104400000000 : ℝ)*(10819/100000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (1304579225564917/1305000000000000 : ℝ)+2*(181314683/104400000000 : ℝ)*(10819/100000 : ℝ)=(4000213445069/4000000000000 : ℝ) by norm_num, show 1+2*(10942831223658663/100000000000000000000 : ℝ)=(50010942831223658663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9708705593724713/25000000000000000000 : ℝ)+(10942831223658663/100000000000000000000 : ℝ) ≤ ((1304579225564917/1305000000000000 : ℝ)+(181314683/104400000000 : ℝ)*((7367/50000 : ℝ)+(10819/100000 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (1304579225564917/1305000000000000 : ℝ)+(181314683/104400000000 : ℝ)*((7367/50000 : ℝ)+(10819/100000 : ℝ))=(8000970834187/8000000000000 : ℝ) by norm_num, show 1+(9708705593724713/25000000000000000000 : ℝ)+(10942831223658663/100000000000000000000 : ℝ)=(20009955530719711503/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9708705593724713/25000000000000000000 : ℝ) ≤ ((1304579225564917/1305000000000000 : ℝ)+2*(181314683/104400000000 : ℝ)*(7367/50000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (1304579225564917/1305000000000000 : ℝ)+2*(181314683/104400000000 : ℝ)*(7367/50000 : ℝ)=(2000378694559/2000000000000 : ℝ) by norm_num, show 1+2*(9708705593724713/25000000000000000000 : ℝ)=(12509708705593724713/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1304579225564917/1305000000000000 : ℝ)*(X 1 0+X 2 0)+(181314683/104400000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (10819/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (1304579225564917/1305000000000000 : ℝ)) (alpha := (181314683/104400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1304579225564917/1305000000000000 : ℝ)*(X 0 1+X 2 1)+(181314683/104400000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (10819/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (1304579225564917/1305000000000000 : ℝ)) (alpha := (181314683/104400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1304579225564917/1305000000000000 : ℝ)*(X 0 2+X 1 2)+(181314683/104400000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (10819/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (1304579225564917/1305000000000000 : ℝ)) (alpha := (181314683/104400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2135555737/10000000000 : ℝ)*X 0 0+(107978933/200000000 : ℝ)*X 0 1+(5260042687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069255079/2000000000 : ℝ)*X 1 0+(-1103050549/5000000000 : ℝ)*X 1 1+(5260042669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42770203/80000000 : ℝ)*X 2 0+(2630021349/5000000000 : ℝ)*X 2 1+(-1103050543/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355227799/10000000000 : ℝ)*X 0 0+(4217494013/10000000000 : ℝ)*X 0 1+(4497367411/10000000000 : ℝ)*X 0 2+(4355227799/10000000000 : ℝ)*X 1 0+(4217494013/10000000000 : ℝ)*X 1 1+(4497367411/10000000000 : ℝ)*X 1 2+(4355227799/10000000000 : ℝ)*X 2 0+(4217494013/10000000000 : ℝ)*X 2 1+(4497367411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135562359/10000000000 : ℝ)*X 0 0+(5260430839/10000000000 : ℝ)*X 0 1+(2699278413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327730093/2500000000 : ℝ)*X 1 0+(-516896737/2500000000 : ℝ)*X 1 1+(5398556861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062184059/2000000000 : ℝ)*X 2 0+(539855697/1000000000 : ℝ)*X 2 1+(-258448363/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177620443/5000000000 : ℝ)*X 0 0+(1124146347/2500000000 : ℝ)*X 0 1+(4218279137/10000000000 : ℝ)*X 0 2+(2177620443/5000000000 : ℝ)*X 1 0+(1124146347/2500000000 : ℝ)*X 1 1+(4218279137/10000000000 : ℝ)*X 1 2+(2177620443/5000000000 : ℝ)*X 2 0+(1124146347/2500000000 : ℝ)*X 2 1+(4218279137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50977057926809726392861/7250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10432101/800000000000 : ℝ)*(base19) + (68221329/6250000000000 : ℝ)*(base23) + (49597239/50000000000000 : ℝ)*(lower2) + (36073711/20000000000000 : ℝ)*(upper3) + (54486091/100000000000000 : ℝ)*(upper5) + (5386179481100751/100000000000000 : ℝ)*(major0) + (5386179481100751/100000000000000 : ℝ)*(major1) + (5386179481100751/100000000000000 : ℝ)*(major2) + (7199252452481029/100000000000000 : ℝ)*(sp0) + (1439856362918197/20000000000000 : ℝ)*(sp1) + (1439856405412469/20000000000000 : ℝ)*(sp2) + (714611650364559/20000000000000 : ℝ)*(sp3) + (1533306129/5000000000000 : ℝ)*(sp4) + (17357397807/100000000000000 : ℝ)*(sp7) + (1786537804610301/50000000000000 : ℝ)*(f.failure) + (719928311860361/10000000000000 : ℝ)*(f.sum) + (116505695717/21750000000000000000000000 : ℝ)*base66 + (416041421974889/43500000000000000000000000000 : ℝ)*base67 + (591207901183889/43500000000000000000000000000 : ℝ)*base69 + (719261222228611/43500000000000000000000000000 : ℝ)*base72 + (409736680577/87000000000000000000000000 : ℝ)*base74 + (805518352336889/43500000000000000000000000000 : ℝ)*base75 + (4510125278611/43500000000000000000000000000 : ℝ)*base78 + (933097240684889/43500000000000000000000000000 : ℝ)*base79 + (8138653519/2718750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (8934393/5000000000000000000000 : ℝ)*base90 + (8934393/5000000000000000000000 : ℝ)*base92 + (8934393/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10768004328547026435749/1359375000000000000000000000 : ℝ) := by norm_num
    linear_combination (59869587/4000000000000 : ℝ)*(base19) + (1459648601/100000000000000 : ℝ)*(base23) + (31173203/12500000000000 : ℝ)*(upper3) + (3502299/25000000000000 : ℝ)*(lower4) + (72992921/50000000000000 : ℝ)*(upper5) + (5416463648691899/100000000000000 : ℝ)*(major0) + (5416463648691899/100000000000000 : ℝ)*(major1) + (5416463648691899/100000000000000 : ℝ)*(major2) + (6709345587/20000000000000 : ℝ)*(sp1) + (1243126847/3125000000000 : ℝ)*(sp2) + (1447952311752577/20000000000000 : ℝ)*(sp4) + (3619863257647637/50000000000000 : ℝ)*(sp5) + (7239720319055179/100000000000000 : ℝ)*(sp6) + (1796582737288943/50000000000000 : ℝ)*(sp7) + (1796582737288943/50000000000000 : ℝ)*(f.failure) + (1447952311752577/20000000000000 : ℝ)*(f.sum) + (382241916509/261000000000000000000000000 : ℝ)*base65 + (851523987711617/130500000000000000000000000000 : ℝ)*base68 + (1408654174563883/130500000000000000000000000000 : ℝ)*base69 + (1179879732725383/130500000000000000000000000000 : ℝ)*base71 + (76755918931/16312500000000000000000000 : ℝ)*base74 + (965524404884383/130500000000000000000000000000 : ℝ)*base75 + (239739390689383/130500000000000000000000000000 : ℝ)*base77 + (2350155220524883/130500000000000000000000000000 : ℝ)*base79 + (12262306877/65250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9856899/5000000000000000000000 : ℝ)*base90 + (9856899/5000000000000000000000 : ℝ)*base92 + (9856899/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1207_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1207_s5_0 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068031041/5000000000 : ℝ)*x 0 + (539326207/1000000000 : ℝ)*x 1 + (2632697367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068031041/5000000000 : ℝ)^525 ≤ (6492907695651/50000000000000 : ℝ)^397 := by
    have hnat : (1068031041 : ℕ)^525*50000000000000^397 ≤ 6492907695651^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068031041 5000000000 6492907695651 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539326207/1000000000 : ℝ)^525 ≤ (44197285047147/100000000000000 : ℝ)^397 := by
    have hnat : (539326207 : ℕ)^525*100000000000000^397 ≤ 44197285047147^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539326207 1000000000 44197285047147 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632697367/5000000000 : ℝ)^525 ≤ (21408449772459/50000000000000 : ℝ)^397 := by
    have hnat : (2632697367 : ℕ)^525*50000000000000^397 ≤ 21408449772459^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632697367 5000000000 21408449772459 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068031041/5000000000 : ℝ), (539326207/1000000000 : ℝ), (2632697367/5000000000 : ℝ)] ![(6492907695651/50000000000000 : ℝ), (44197285047147/100000000000000 : ℝ), (21408449772459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068031041/5000000000 : ℝ)|^525 ≤ (6492907695651/50000000000000 : ℝ)^397
        have hw : |(-1068031041/5000000000 : ℝ)|=(1068031041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539326207/1000000000 : ℝ)|^525 ≤ (44197285047147/100000000000000 : ℝ)^397
        have hw : |(539326207/1000000000 : ℝ)|=(539326207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632697367/5000000000 : ℝ)|^525 ≤ (21408449772459/50000000000000 : ℝ)^397
        have hw : |(2632697367/5000000000 : ℝ)|=(2632697367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_1 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1068968367/2000000000 : ℝ)*x 0 + (-2200922383/10000000000 : ℝ)*x 1 + (1316348683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068968367/2000000000 : ℝ)^525 ≤ (21836655692347/50000000000000 : ℝ)^397 := by
    have hnat : (1068968367 : ℕ)^525*50000000000000^397 ≤ 21836655692347^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068968367 2000000000 21836655692347 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200922383/10000000000 : ℝ)^525 ≤ (3377447269457/25000000000000 : ℝ)^397 := by
    have hnat : (2200922383 : ℕ)^525*25000000000000^397 ≤ 3377447269457^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200922383 10000000000 3377447269457 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316348683/2500000000 : ℝ)^525 ≤ (42816899523411/100000000000000 : ℝ)^397 := by
    have hnat : (1316348683 : ℕ)^525*100000000000000^397 ≤ 42816899523411^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316348683 2500000000 42816899523411 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068968367/2000000000 : ℝ), (-2200922383/10000000000 : ℝ), (1316348683/2500000000 : ℝ)] ![(21836655692347/50000000000000 : ℝ), (3377447269457/25000000000000 : ℝ), (42816899523411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068968367/2000000000 : ℝ)|^525 ≤ (21836655692347/50000000000000 : ℝ)^397
        have hw : |(1068968367/2000000000 : ℝ)|=(1068968367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200922383/10000000000 : ℝ)|^525 ≤ (3377447269457/25000000000000 : ℝ)^397
        have hw : |(-2200922383/10000000000 : ℝ)|=(2200922383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316348683/2500000000 : ℝ)|^525 ≤ (42816899523411/100000000000000 : ℝ)^397
        have hw : |(1316348683/2500000000 : ℝ)|=(1316348683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_2 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344841839/10000000000 : ℝ)*x 0 + (5265394727/10000000000 : ℝ)*x 1 + (-137557649/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344841839/10000000000 : ℝ)^525 ≤ (43673311427917/100000000000000 : ℝ)^397 := by
    have hnat : (5344841839 : ℕ)^525*100000000000000^397 ≤ 43673311427917^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344841839 10000000000 43673311427917 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265394727/10000000000 : ℝ)^525 ≤ (42816899469643/100000000000000 : ℝ)^397 := by
    have hnat : (5265394727 : ℕ)^525*100000000000000^397 ≤ 42816899469643^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265394727 10000000000 42816899469643 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137557649/625000000 : ℝ)^525 ≤ (2701957817189/20000000000000 : ℝ)^397 := by
    have hnat : (137557649 : ℕ)^525*20000000000000^397 ≤ 2701957817189^397*625000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137557649 625000000 2701957817189 20000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344841839/10000000000 : ℝ), (5265394727/10000000000 : ℝ), (-137557649/625000000 : ℝ)] ![(43673311427917/100000000000000 : ℝ), (42816899469643/100000000000000 : ℝ), (2701957817189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344841839/10000000000 : ℝ)|^525 ≤ (43673311427917/100000000000000 : ℝ)^397
        have hw : |(5344841839/10000000000 : ℝ)|=(5344841839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265394727/10000000000 : ℝ)|^525 ≤ (42816899469643/100000000000000 : ℝ)^397
        have hw : |(5265394727/10000000000 : ℝ)|=(5265394727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137557649/625000000 : ℝ)|^525 ≤ (2701957817189/20000000000000 : ℝ)^397
        have hw : |(-137557649/625000000 : ℝ)|=(137557649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_3 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (871105089/2000000000 : ℝ)*x 0 + (2114287217/5000000000 : ℝ)*x 1 + (4486210527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871105089/2000000000 : ℝ)^525 ≤ (8329150175723/25000000000000 : ℝ)^397 := by
    have hnat : (871105089 : ℕ)^525*25000000000000^397 ≤ 8329150175723^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871105089 2000000000 8329150175723 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114287217/5000000000 : ℝ)^525 ≤ (32038497390407/100000000000000 : ℝ)^397 := by
    have hnat : (2114287217 : ℕ)^525*100000000000000^397 ≤ 32038497390407^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114287217 5000000000 32038497390407 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486210527/10000000000 : ℝ)^525 ≤ (17322450944563/50000000000000 : ℝ)^397 := by
    have hnat : (4486210527 : ℕ)^525*50000000000000^397 ≤ 17322450944563^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486210527 10000000000 17322450944563 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871105089/2000000000 : ℝ), (2114287217/5000000000 : ℝ), (4486210527/10000000000 : ℝ)] ![(8329150175723/25000000000000 : ℝ), (32038497390407/100000000000000 : ℝ), (17322450944563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871105089/2000000000 : ℝ)|^525 ≤ (8329150175723/25000000000000 : ℝ)^397
        have hw : |(871105089/2000000000 : ℝ)|=(871105089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114287217/5000000000 : ℝ)|^525 ≤ (32038497390407/100000000000000 : ℝ)^397
        have hw : |(2114287217/5000000000 : ℝ)|=(2114287217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486210527/10000000000 : ℝ)|^525 ≤ (17322450944563/50000000000000 : ℝ)^397
        have hw : |(4486210527/10000000000 : ℝ)|=(4486210527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_4 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-213606683/1000000000 : ℝ)*x 0 + (5265724169/10000000000 : ℝ)*x 1 + (1078586329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213606683/1000000000 : ℝ)^525 ≤ (202903961913/1562500000000 : ℝ)^397 := by
    have hnat : (213606683 : ℕ)^525*1562500000000^397 ≤ 202903961913^397*1000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213606683 1000000000 202903961913 1562500000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265724169/10000000000 : ℝ)^525 ≤ (21410221093169/50000000000000 : ℝ)^397 := by
    have hnat : (5265724169 : ℕ)^525*50000000000000^397 ≤ 21410221093169^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265724169 10000000000 21410221093169 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078586329/2000000000 : ℝ)^525 ≤ (5524213029441/12500000000000 : ℝ)^397 := by
    have hnat : (1078586329 : ℕ)^525*12500000000000^397 ≤ 5524213029441^397*2000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078586329 2000000000 5524213029441 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213606683/1000000000 : ℝ), (5265724169/10000000000 : ℝ), (1078586329/2000000000 : ℝ)] ![(202903961913/1562500000000 : ℝ), (21410221093169/50000000000000 : ℝ), (5524213029441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213606683/1000000000 : ℝ)|^525 ≤ (202903961913/1562500000000 : ℝ)^397
        have hw : |(-213606683/1000000000 : ℝ)|=(213606683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265724169/10000000000 : ℝ)|^525 ≤ (21410221093169/50000000000000 : ℝ)^397
        have hw : |(5265724169/10000000000 : ℝ)|=(5265724169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078586329/2000000000 : ℝ)|^525 ≤ (5524213029441/12500000000000 : ℝ)^397
        have hw : |(1078586329/2000000000 : ℝ)|=(1078586329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_5 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328073717/2500000000 : ℝ)*x 0 + (-1036692577/5000000000 : ℝ)*x 1 + (2696465809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328073717/2500000000 : ℝ)^525 ≤ (21660983323609/50000000000000 : ℝ)^397 := by
    have hnat : (1328073717 : ℕ)^525*50000000000000^397 ≤ 21660983323609^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328073717 2500000000 21660983323609 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036692577/5000000000 : ℝ)^525 ≤ (12484329394761/100000000000000 : ℝ)^397 := by
    have hnat : (1036692577 : ℕ)^525*100000000000000^397 ≤ 12484329394761^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036692577 5000000000 12484329394761 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696465809/5000000000 : ℝ)^525 ≤ (11048425985733/25000000000000 : ℝ)^397 := by
    have hnat : (2696465809 : ℕ)^525*25000000000000^397 ≤ 11048425985733^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696465809 5000000000 11048425985733 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328073717/2500000000 : ℝ), (-1036692577/5000000000 : ℝ), (2696465809/5000000000 : ℝ)] ![(21660983323609/50000000000000 : ℝ), (12484329394761/100000000000000 : ℝ), (11048425985733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328073717/2500000000 : ℝ)|^525 ≤ (21660983323609/50000000000000 : ℝ)^397
        have hw : |(1328073717/2500000000 : ℝ)|=(1328073717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036692577/5000000000 : ℝ)|^525 ≤ (12484329394761/100000000000000 : ℝ)^397
        have hw : |(-1036692577/5000000000 : ℝ)|=(1036692577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696465809/5000000000 : ℝ)|^525 ≤ (11048425985733/25000000000000 : ℝ)^397
        have hw : |(2696465809/5000000000 : ℝ)|=(2696465809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_6 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328073647/2500000000 : ℝ)*x 0 + (5392931969/10000000000 : ℝ)*x 1 + (-64793283/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328073647/2500000000 : ℝ)^525 ≤ (21660981813797/50000000000000 : ℝ)^397 := by
    have hnat : (1328073647 : ℕ)^525*50000000000000^397 ≤ 21660981813797^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328073647 2500000000 21660981813797 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392931969/10000000000 : ℝ)^525 ≤ (44193707746677/100000000000000 : ℝ)^397 := by
    have hnat : (5392931969 : ℕ)^525*100000000000000^397 ≤ 44193707746677^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392931969 10000000000 44193707746677 100000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64793283/312500000 : ℝ)^525 ≤ (3121082153607/25000000000000 : ℝ)^397 := by
    have hnat : (64793283 : ℕ)^525*25000000000000^397 ≤ 3121082153607^397*312500000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64793283 312500000 3121082153607 25000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328073647/2500000000 : ℝ), (5392931969/10000000000 : ℝ), (-64793283/312500000 : ℝ)] ![(21660981813797/50000000000000 : ℝ), (44193707746677/100000000000000 : ℝ), (3121082153607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328073647/2500000000 : ℝ)|^525 ≤ (21660981813797/50000000000000 : ℝ)^397
        have hw : |(1328073647/2500000000 : ℝ)|=(1328073647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392931969/10000000000 : ℝ)|^525 ≤ (44193707746677/100000000000000 : ℝ)^397
        have hw : |(5392931969/10000000000 : ℝ)|=(5392931969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64793283/312500000 : ℝ)|^525 ≤ (3121082153607/25000000000000 : ℝ)^397
        have hw : |(-64793283/312500000 : ℝ)|=(64793283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1207_s5_7 (p : ℝ) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4355535847/10000000000 : ℝ)*x 0 + (2242773659/5000000000 : ℝ)*x 1 + (1057309969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355535847/10000000000 : ℝ)^525 ≤ (4164588240593/12500000000000 : ℝ)^397 := by
    have hnat : (4355535847 : ℕ)^525*12500000000000^397 ≤ 4164588240593^397*10000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355535847 10000000000 4164588240593 12500000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242773659/5000000000 : ℝ)^525 ≤ (1082441533893/3125000000000 : ℝ)^397 := by
    have hnat : (2242773659 : ℕ)^525*3125000000000^397 ≤ 1082441533893^397*5000000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242773659 5000000000 1082441533893 3125000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057309969/2500000000 : ℝ)^525 ≤ (16022582484793/50000000000000 : ℝ)^397 := by
    have hnat : (1057309969 : ℕ)^525*50000000000000^397 ≤ 16022582484793^397*2500000000^525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057309969 2500000000 16022582484793 50000000000000 525 397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (525/128 : ℝ)) 525 397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355535847/10000000000 : ℝ), (2242773659/5000000000 : ℝ), (1057309969/2500000000 : ℝ)] ![(4164588240593/12500000000000 : ℝ), (1082441533893/3125000000000 : ℝ), (16022582484793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355535847/10000000000 : ℝ)|^525 ≤ (4164588240593/12500000000000 : ℝ)^397
        have hw : |(4355535847/10000000000 : ℝ)|=(4355535847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242773659/5000000000 : ℝ)|^525 ≤ (1082441533893/3125000000000 : ℝ)^397
        have hw : |(2242773659/5000000000 : ℝ)|=(2242773659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057309969/2500000000 : ℝ)|^525 ≤ (16022582484793/50000000000000 : ℝ)^397
        have hw : |(1057309969/2500000000 : ℝ)|=(1057309969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1207_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11407/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11293/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11293/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11293/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11293/100000 : ℝ) ^ (8399/2048 : ℝ) ≤ (3261675594840253/25000000000000000000 : ℝ) := by
    have hpowers : (11293/100000 : ℝ)^8399 ≤ (3261675594840253/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11293 : ℕ)^8399*25000000000000000000^2048 ≤ 3261675594840253^2048*100000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11293 100000 3261675594840253 25000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11293/100000 : ℝ)) (X := (3261675594840253/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8399/2048 : ℝ) ≤ (1685878057461343/5000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8399 ≤ (1685878057461343/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8399*5000000000000000000^2048 ≤ 1685878057461343^2048*20000^8399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 1685878057461343 5000000000000000000 8399 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (1685878057461343/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503261675594840253/12500000000000000000 : ℝ) ≤ (500031809752199/500000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (12503261675594840253/12500000000000000000 : ℝ)^2048 ≤ (500031809752199/500000000000000 : ℝ)^8399 := by
      have hnat : (12503261675594840253 : ℕ)^2048*500000000000000^8399 ≤ 500031809752199^8399*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503261675594840253 12500000000000000000 500031809752199 500000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500031809752199/500000000000000 : ℝ)) (X := (12503261675594840253/12500000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126461383235268371/3125000000000000000 : ℝ) ≤ (2500285022868789/2500000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (3126461383235268371/3125000000000000000 : ℝ)^2048 ≤ (2500285022868789/2500000000000000 : ℝ)^8399 := by
      have hnat : (3126461383235268371 : ℕ)^2048*2500000000000000^8399 ≤ 2500285022868789^8399*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126461383235268371 3125000000000000000 2500285022868789 2500000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500285022868789/2500000000000000 : ℝ)) (X := (3126461383235268371/3125000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501685878057461343/2500000000000000000 : ℝ) ≤ (2500410996976583/2500000000000000 : ℝ) ^ (8399/2048 : ℝ) := by
    have hpowers : (2501685878057461343/2500000000000000000 : ℝ)^2048 ≤ (2500410996976583/2500000000000000 : ℝ)^8399 := by
      have hnat : (2501685878057461343 : ℕ)^2048*2500000000000000^8399 ≤ 2500410996976583^8399*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501685878057461343 2500000000000000000 2500410996976583 2500000000000000 2048 8399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500410996976583/2500000000000000 : ℝ)) (X := (2501685878057461343/2500000000000000000 : ℝ)) (by norm_num) 8399 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3261675594840253/25000000000000000000 : ℝ) ≤ ((3676311335128106003/3677500000000000000 : ℝ)+2*(62987053897/36775000000000 : ℝ)*(11293/100000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (3676311335128106003/3677500000000000000 : ℝ)+2*(62987053897/36775000000000 : ℝ)*(11293/100000 : ℝ)=(500031809752199/500000000000000 : ℝ) by norm_num, show 1+2*(3261675594840253/25000000000000000000 : ℝ)=(12503261675594840253/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1685878057461343/5000000000000000000 : ℝ)+(3261675594840253/25000000000000000000 : ℝ) ≤ ((3676311335128106003/3677500000000000000 : ℝ)+(62987053897/36775000000000 : ℝ)*((2847/20000 : ℝ)+(11293/100000 : ℝ)))^(8399/2048 : ℝ) := by
    rw [show (3676311335128106003/3677500000000000000 : ℝ)+(62987053897/36775000000000 : ℝ)*((2847/20000 : ℝ)+(11293/100000 : ℝ))=(2500285022868789/2500000000000000 : ℝ) by norm_num, show 1+(1685878057461343/5000000000000000000 : ℝ)+(3261675594840253/25000000000000000000 : ℝ)=(3126461383235268371/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1685878057461343/5000000000000000000 : ℝ) ≤ ((3676311335128106003/3677500000000000000 : ℝ)+2*(62987053897/36775000000000 : ℝ)*(2847/20000 : ℝ))^(8399/2048 : ℝ) := by
    rw [show (3676311335128106003/3677500000000000000 : ℝ)+2*(62987053897/36775000000000 : ℝ)*(2847/20000 : ℝ)=(2500410996976583/2500000000000000 : ℝ) by norm_num, show 1+2*(1685878057461343/5000000000000000000 : ℝ)=(2501685878057461343/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3676311335128106003/3677500000000000000 : ℝ)*(X 1 0+X 2 0)+(62987053897/36775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3676311335128106003/3677500000000000000 : ℝ)) (alpha := (62987053897/36775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3676311335128106003/3677500000000000000 : ℝ)*(X 0 1+X 2 1)+(62987053897/36775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3676311335128106003/3677500000000000000 : ℝ)) (alpha := (62987053897/36775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3676311335128106003/3677500000000000000 : ℝ)*(X 0 2+X 1 2)+(62987053897/36775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8399/2048 : ℝ)) (lo := (11293/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3676311335128106003/3677500000000000000 : ℝ)) (alpha := (62987053897/36775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068031041/5000000000 : ℝ)*X 0 0+(539326207/1000000000 : ℝ)*X 0 1+(2632697367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068968367/2000000000 : ℝ)*X 1 0+(-2200922383/10000000000 : ℝ)*X 1 1+(1316348683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344841839/10000000000 : ℝ)*X 2 0+(5265394727/10000000000 : ℝ)*X 2 1+(-137557649/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871105089/2000000000 : ℝ)*X 0 0+(2114287217/5000000000 : ℝ)*X 0 1+(4486210527/10000000000 : ℝ)*X 0 2+(871105089/2000000000 : ℝ)*X 1 0+(2114287217/5000000000 : ℝ)*X 1 1+(4486210527/10000000000 : ℝ)*X 1 2+(871105089/2000000000 : ℝ)*X 2 0+(2114287217/5000000000 : ℝ)*X 2 1+(4486210527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213606683/1000000000 : ℝ)*X 0 0+(5265724169/10000000000 : ℝ)*X 0 1+(1078586329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328073717/2500000000 : ℝ)*X 1 0+(-1036692577/5000000000 : ℝ)*X 1 1+(2696465809/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328073647/2500000000 : ℝ)*X 2 0+(5392931969/10000000000 : ℝ)*X 2 1+(-64793283/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355535847/10000000000 : ℝ)*X 0 0+(2242773659/5000000000 : ℝ)*X 0 1+(1057309969/2500000000 : ℝ)*X 0 2+(4355535847/10000000000 : ℝ)*X 1 0+(2242773659/5000000000 : ℝ)*X 1 1+(1057309969/2500000000 : ℝ)*X 1 2+(4355535847/10000000000 : ℝ)*X 2 0+(2242773659/5000000000 : ℝ)*X 2 1+(1057309969/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1207_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (667184795916456275269480827/91937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (280074589/20000000000000 : ℝ)*(base19) + (1310254899/100000000000000 : ℝ)*(base23) + (51294941/100000000000000 : ℝ)*(lower2) + (182146877/100000000000000 : ℝ)*(upper3) + (110554397/100000000000000 : ℝ)*(upper5) + (5851082506774797/100000000000000 : ℝ)*(major0) + (5851082506774797/100000000000000 : ℝ)*(major1) + (5851082506774797/100000000000000 : ℝ)*(major2) + (3910322456667709/50000000000000 : ℝ)*(sp0) + (1564136219009437/20000000000000 : ℝ)*(sp1) + (782068118516523/10000000000000 : ℝ)*(sp2) + (388146196571561/10000000000000 : ℝ)*(sp3) + (37582084711/100000000000000 : ℝ)*(sp4) + (10155257947/50000000000000 : ℝ)*(sp7) + (242592642264469/6250000000000 : ℝ)*(f.failure) + (7820682495420129/100000000000000 : ℝ)*(f.sum) + (15105999325687/3677500000000000000000000000 : ℝ)*base66 + (1240723291700456391/367750000000000000000000000000000 : ℝ)*base67 + (594541834332956391/367750000000000000000000000000000 : ℝ)*base69 + (174148744717456391/367750000000000000000000000000000 : ℝ)*base71 + (31439201841199/7355000000000000000000000000 : ℝ)*base74 + (647879921802206391/367750000000000000000000000000000 : ℝ)*base75 + (4145102033068793609/367750000000000000000000000000000 : ℝ)*base78 + (703563079310206391/367750000000000000000000000000000 : ℝ)*base79 + (14876602894133/3677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2697217/625000000000000000000 : ℝ)*base90 + (2697217/625000000000000000000 : ℝ)*base92 + (2697217/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (832965933768840040981299123/91937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1684861823/100000000000000 : ℝ)*(base19) + (2206919797/100000000000000 : ℝ)*(base23) + (21439223/10000000000000 : ℝ)*(upper3) + (19503157/5000000000000 : ℝ)*(lower4) + (2940678815074653/50000000000000 : ℝ)*(major0) + (2940678815074653/50000000000000 : ℝ)*(major1) + (2940678815074653/50000000000000 : ℝ)*(major2) + (2649282731/6250000000000 : ℝ)*(sp1) + (75380664971/100000000000000 : ℝ)*(sp2) + (39437893/3125000000000 : ℝ)*(sp3) + (3930574408222087/50000000000000 : ℝ)*(sp4) + (1572220948611731/20000000000000 : ℝ)*(sp5) + (3930535614429703/50000000000000 : ℝ)*(sp6) + (1950782439918719/50000000000000 : ℝ)*(sp7) + (1950783070925007/50000000000000 : ℝ)*(f.failure) + (3930574408222087/50000000000000 : ℝ)*(f.sum) + (9007661590199/3677500000000000000000000000 : ℝ)*base65 + (2119574879034791959/183875000000000000000000000000000 : ℝ)*base67 + (153917549329708041/183875000000000000000000000000000 : ℝ)*base70 + (1669866949738291959/183875000000000000000000000000000 : ℝ)*base71 + (9692388928861/3677500000000000000000000000 : ℝ)*base74 + (229883121088708041/183875000000000000000000000000000 : ℝ)*base76 + (2644383911452416959/183875000000000000000000000000000 : ℝ)*base77 + (2044238179450416959/183875000000000000000000000000000 : ℝ)*base79 + (827406072517/459687500000000000000000000 : ℝ)*base82 + (10820451/5000000000000000000000 : ℝ)*base90 + (10820451/5000000000000000000000 : ℝ)*base92 + (10820451/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1207_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11407/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1207_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1207_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11407/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1207_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1207_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1207_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8399/2048 : ℝ) ≤ p) (hpb : p ≤ (525/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150743507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11407/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1207_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
