-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:55:35.505976+00:00
-- url     : https://prove2.me/submissions/2066afbe-ce2e-4cf3-b1c7-50511348eab2

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
theorem support_rectangle_w1263_s0_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854097613/10000000000 : ℝ)*x 0 + (6026784779/10000000000 : ℝ)*x 1 + (2397791071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854097613/10000000000 : ℝ)^1057 ≤ (10820003633313/100000000000000 : ℝ)^801 := by
    have hnat : (1854097613 : ℕ)^1057*100000000000000^801 ≤ 10820003633313^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854097613 10000000000 10820003633313 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6026784779/10000000000 : ℝ)^1057 ≤ (1601957458631/3125000000000 : ℝ)^801 := by
    have hnat : (6026784779 : ℕ)^1057*3125000000000^801 ≤ 1601957458631^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026784779 10000000000 1601957458631 3125000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397791071/5000000000 : ℝ)^1057 ≤ (37917357679187/100000000000000 : ℝ)^801 := by
    have hnat : (2397791071 : ℕ)^1057*100000000000000^801 ≤ 37917357679187^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397791071 5000000000 37917357679187 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854097613/10000000000 : ℝ), (6026784779/10000000000 : ℝ), (2397791071/5000000000 : ℝ)] ![(10820003633313/100000000000000 : ℝ), (1601957458631/3125000000000 : ℝ), (37917357679187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854097613/10000000000 : ℝ)|^1057 ≤ (10820003633313/100000000000000 : ℝ)^801
        have hw : |(-1854097613/10000000000 : ℝ)|=(1854097613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6026784779/10000000000 : ℝ)|^1057 ≤ (1601957458631/3125000000000 : ℝ)^801
        have hw : |(6026784779/10000000000 : ℝ)|=(6026784779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397791071/5000000000 : ℝ)|^1057 ≤ (37917357679187/100000000000000 : ℝ)^801
        have hw : |(2397791071/5000000000 : ℝ)|=(2397791071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (688747049/1250000000 : ℝ)*x 0 + (-511477209/2000000000 : ℝ)*x 1 + (2397791057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688747049/1250000000 : ℝ)^1057 ≤ (1138573505971/2500000000000 : ℝ)^801 := by
    have hnat : (688747049 : ℕ)^1057*2500000000000^801 ≤ 1138573505971^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688747049 1250000000 1138573505971 2500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511477209/2000000000 : ℝ)^1057 ≤ (16539702357839/100000000000000 : ℝ)^801 := by
    have hnat : (511477209 : ℕ)^1057*100000000000000^801 ≤ 16539702357839^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511477209 2000000000 16539702357839 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397791057/5000000000 : ℝ)^1057 ≤ (18958678693521/50000000000000 : ℝ)^801 := by
    have hnat : (2397791057 : ℕ)^1057*50000000000000^801 ≤ 18958678693521^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397791057 5000000000 18958678693521 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688747049/1250000000 : ℝ), (-511477209/2000000000 : ℝ), (2397791057/5000000000 : ℝ)] ![(1138573505971/2500000000000 : ℝ), (16539702357839/100000000000000 : ℝ), (18958678693521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688747049/1250000000 : ℝ)|^1057 ≤ (1138573505971/2500000000000 : ℝ)^801
        have hw : |(688747049/1250000000 : ℝ)|=(688747049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511477209/2000000000 : ℝ)|^1057 ≤ (16539702357839/100000000000000 : ℝ)^801
        have hw : |(-511477209/2000000000 : ℝ)|=(511477209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397791057/5000000000 : ℝ)|^1057 ≤ (18958678693521/50000000000000 : ℝ)^801
        have hw : |(2397791057/5000000000 : ℝ)|=(2397791057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5509976421/10000000000 : ℝ)*x 0 + (4795582113/10000000000 : ℝ)*x 1 + (-2557386009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509976421/10000000000 : ℝ)^1057 ≤ (45542940555149/100000000000000 : ℝ)^801 := by
    have hnat : (5509976421 : ℕ)^1057*100000000000000^801 ≤ 45542940555149^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509976421 10000000000 45542940555149 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795582113/10000000000 : ℝ)^1057 ≤ (37917357376609/100000000000000 : ℝ)^801 := by
    have hnat : (4795582113 : ℕ)^1057*100000000000000^801 ≤ 37917357376609^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795582113 10000000000 37917357376609 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2557386009/10000000000 : ℝ)^1057 ≤ (82698510253/500000000000 : ℝ)^801 := by
    have hnat : (2557386009 : ℕ)^1057*500000000000^801 ≤ 82698510253^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557386009 10000000000 82698510253 500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509976421/10000000000 : ℝ), (4795582113/10000000000 : ℝ), (-2557386009/10000000000 : ℝ)] ![(45542940555149/100000000000000 : ℝ), (37917357376609/100000000000000 : ℝ), (82698510253/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509976421/10000000000 : ℝ)|^1057 ≤ (45542940555149/100000000000000 : ℝ)^801
        have hw : |(5509976421/10000000000 : ℝ)|=(5509976421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795582113/10000000000 : ℝ)|^1057 ≤ (37917357376609/100000000000000 : ℝ)^801
        have hw : |(4795582113/10000000000 : ℝ)|=(4795582113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2557386009/10000000000 : ℝ)|^1057 ≤ (82698510253/500000000000 : ℝ)^801
        have hw : |(-2557386009/10000000000 : ℝ)|=(2557386009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4191377137/10000000000 : ℝ)*x 0 + (12464487/40000000 : ℝ)*x 1 + (5623834249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191377137/10000000000 : ℝ)^1057 ≤ (31744008417313/100000000000000 : ℝ)^801 := by
    have hnat : (4191377137 : ℕ)^1057*100000000000000^801 ≤ 31744008417313^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191377137 10000000000 31744008417313 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12464487/40000000 : ℝ)^1057 ≤ (5366774422809/25000000000000 : ℝ)^801 := by
    have hnat : (12464487 : ℕ)^1057*25000000000000^801 ≤ 5366774422809^801*40000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12464487 40000000 5366774422809 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5623834249/10000000000 : ℝ)^1057 ≤ (5848611735563/12500000000000 : ℝ)^801 := by
    have hnat : (5623834249 : ℕ)^1057*12500000000000^801 ≤ 5848611735563^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5623834249 10000000000 5848611735563 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191377137/10000000000 : ℝ), (12464487/40000000 : ℝ), (5623834249/10000000000 : ℝ)] ![(31744008417313/100000000000000 : ℝ), (5366774422809/25000000000000 : ℝ), (5848611735563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191377137/10000000000 : ℝ)|^1057 ≤ (31744008417313/100000000000000 : ℝ)^801
        have hw : |(4191377137/10000000000 : ℝ)|=(4191377137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12464487/40000000 : ℝ)|^1057 ≤ (5366774422809/25000000000000 : ℝ)^801
        have hw : |(12464487/40000000 : ℝ)|=(12464487/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5623834249/10000000000 : ℝ)|^1057 ≤ (5848611735563/12500000000000 : ℝ)^801
        have hw : |(5623834249/10000000000 : ℝ)|=(5623834249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1858895661/10000000000 : ℝ)*x 0 + (603409281/1250000000 : ℝ)*x 1 + (5993971901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1858895661/10000000000 : ℝ)^1057 ≤ (2714241958593/25000000000000 : ℝ)^801 := by
    have hnat : (1858895661 : ℕ)^1057*25000000000000^801 ≤ 2714241958593^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858895661 10000000000 2714241958593 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603409281/1250000000 : ℝ)^1057 ≤ (4781046617343/12500000000000 : ℝ)^801 := by
    have hnat : (603409281 : ℕ)^1057*12500000000000^801 ≤ 4781046617343^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603409281 1250000000 4781046617343 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5993971901/10000000000 : ℝ)^1057 ≤ (6361832401147/12500000000000 : ℝ)^801 := by
    have hnat : (5993971901 : ℕ)^1057*12500000000000^801 ≤ 6361832401147^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993971901 10000000000 6361832401147 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1858895661/10000000000 : ℝ), (603409281/1250000000 : ℝ), (5993971901/10000000000 : ℝ)] ![(2714241958593/25000000000000 : ℝ), (4781046617343/12500000000000 : ℝ), (6361832401147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1858895661/10000000000 : ℝ)|^1057 ≤ (2714241958593/25000000000000 : ℝ)^801
        have hw : |(-1858895661/10000000000 : ℝ)|=(1858895661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603409281/1250000000 : ℝ)|^1057 ≤ (4781046617343/12500000000000 : ℝ)^801
        have hw : |(603409281/1250000000 : ℝ)|=(603409281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5993971901/10000000000 : ℝ)|^1057 ≤ (6361832401147/12500000000000 : ℝ)^801
        have hw : |(5993971901/10000000000 : ℝ)|=(5993971901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5174896653/10000000000 : ℝ)*x 0 + (-1358993839/10000000000 : ℝ)*x 1 + (599397433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174896653/10000000000 : ℝ)^1057 ≤ (5240521756971/12500000000000 : ℝ)^801 := by
    have hnat : (5174896653 : ℕ)^1057*12500000000000^801 ≤ 5240521756971^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174896653 10000000000 5240521756971 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358993839/10000000000 : ℝ)^1057 ≤ (897642439089/12500000000000 : ℝ)^801 := by
    have hnat : (1358993839 : ℕ)^1057*12500000000000^801 ≤ 897642439089^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358993839 10000000000 897642439089 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599397433/1000000000 : ℝ)^1057 ≤ (25447343212689/50000000000000 : ℝ)^801 := by
    have hnat : (599397433 : ℕ)^1057*50000000000000^801 ≤ 25447343212689^801*1000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599397433 1000000000 25447343212689 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174896653/10000000000 : ℝ), (-1358993839/10000000000 : ℝ), (599397433/1000000000 : ℝ)] ![(5240521756971/12500000000000 : ℝ), (897642439089/12500000000000 : ℝ), (25447343212689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174896653/10000000000 : ℝ)|^1057 ≤ (5240521756971/12500000000000 : ℝ)^801
        have hw : |(5174896653/10000000000 : ℝ)|=(5174896653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358993839/10000000000 : ℝ)|^1057 ≤ (897642439089/12500000000000 : ℝ)^801
        have hw : |(-1358993839/10000000000 : ℝ)|=(1358993839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599397433/1000000000 : ℝ)|^1057 ≤ (25447343212689/50000000000000 : ℝ)^801
        have hw : |(599397433/1000000000 : ℝ)|=(599397433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2587448861/5000000000 : ℝ)*x 0 + (5993972317/10000000000 : ℝ)*x 1 + (-679497717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587448861/5000000000 : ℝ)^1057 ≤ (8384837096821/20000000000000 : ℝ)^801 := by
    have hnat : (2587448861 : ℕ)^1057*20000000000000^801 ≤ 8384837096821^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587448861 5000000000 8384837096821 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5993972317/10000000000 : ℝ)^1057 ≤ (6361832983791/12500000000000 : ℝ)^801 := by
    have hnat : (5993972317 : ℕ)^1057*12500000000000^801 ≤ 6361832983791^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993972317 10000000000 6361832983791 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679497717/5000000000 : ℝ)^1057 ≤ (1436230126923/20000000000000 : ℝ)^801 := by
    have hnat : (679497717 : ℕ)^1057*20000000000000^801 ≤ 1436230126923^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679497717 5000000000 1436230126923 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587448861/5000000000 : ℝ), (5993972317/10000000000 : ℝ), (-679497717/5000000000 : ℝ)] ![(8384837096821/20000000000000 : ℝ), (6361832983791/12500000000000 : ℝ), (1436230126923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587448861/5000000000 : ℝ)|^1057 ≤ (8384837096821/20000000000000 : ℝ)^801
        have hw : |(2587448861/5000000000 : ℝ)|=(2587448861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5993972317/10000000000 : ℝ)|^1057 ≤ (6361832983791/12500000000000 : ℝ)^801
        have hw : |(5993972317/10000000000 : ℝ)|=(5993972317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-679497717/5000000000 : ℝ)|^1057 ≤ (1436230126923/20000000000000 : ℝ)^801
        have hw : |(-679497717/5000000000 : ℝ)|=(679497717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s0_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (262572023/625000000 : ℝ)*x 0 + (5559289711/10000000000 : ℝ)*x 1 + (3182948901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262572023/625000000 : ℝ)^1057 ≤ (15920870150269/50000000000000 : ℝ)^801 := by
    have hnat : (262572023 : ℕ)^1057*50000000000000^801 ≤ 15920870150269^801*625000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262572023 625000000 15920870150269 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5559289711/10000000000 : ℝ)^1057 ≤ (4608157881661/10000000000000 : ℝ)^801 := by
    have hnat : (5559289711 : ℕ)^1057*10000000000000^801 ≤ 4608157881661^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559289711 10000000000 4608157881661 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3182948901/10000000000 : ℝ)^1057 ≤ (22076680866479/100000000000000 : ℝ)^801 := by
    have hnat : (3182948901 : ℕ)^1057*100000000000000^801 ≤ 22076680866479^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182948901 10000000000 22076680866479 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262572023/625000000 : ℝ), (5559289711/10000000000 : ℝ), (3182948901/10000000000 : ℝ)] ![(15920870150269/50000000000000 : ℝ), (4608157881661/10000000000000 : ℝ), (22076680866479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262572023/625000000 : ℝ)|^1057 ≤ (15920870150269/50000000000000 : ℝ)^801
        have hw : |(262572023/625000000 : ℝ)|=(262572023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5559289711/10000000000 : ℝ)|^1057 ≤ (4608157881661/10000000000000 : ℝ)^801
        have hw : |(5559289711/10000000000 : ℝ)|=(5559289711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3182948901/10000000000 : ℝ)|^1057 ≤ (22076680866479/100000000000000 : ℝ)^801
        have hw : |(3182948901/10000000000 : ℝ)|=(3182948901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13679/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8455/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8455 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8455*1^2048 ≤ 0^2048*1^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8455/2048 : ℝ) ≤ (284477112228734117/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8455 ≤ (284477112228734117/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8455*12500000000000000000^2048 ≤ 284477112228734117^2048*5^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 284477112228734117 12500000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (284477112228734117/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8455 := by
      have hnat : (1 : ℕ)^2048*1^8455 ≤ 1^8455*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12784477112228734117/12500000000000000000 : ℝ) ≤ (201093130896911/200000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (12784477112228734117/12500000000000000000 : ℝ)^2048 ≤ (201093130896911/200000000000000 : ℝ)^8455 := by
      have hnat : (12784477112228734117 : ℕ)^2048*200000000000000^8455 ≤ 201093130896911^8455*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12784477112228734117 12500000000000000000 201093130896911 200000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201093130896911/200000000000000 : ℝ)) (X := (12784477112228734117/12500000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6534477112228734117/6250000000000000000 : ℝ) ≤ (101093130896911/100000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (6534477112228734117/6250000000000000000 : ℝ)^2048 ≤ (101093130896911/100000000000000 : ℝ)^8455 := by
      have hnat : (6534477112228734117 : ℕ)^2048*100000000000000^8455 ≤ 101093130896911^8455*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6534477112228734117 6250000000000000000 101093130896911 100000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (101093130896911/100000000000000 : ℝ)) (X := (6534477112228734117/6250000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1093130896911/80000000000000 : ℝ)*(0 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1093130896911/80000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(284477112228734117/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1093130896911/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (1 : ℝ)+(1093130896911/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(201093130896911/200000000000000 : ℝ) by norm_num, show 1+(284477112228734117/12500000000000000000 : ℝ)+(0 : ℝ)=(12784477112228734117/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(284477112228734117/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1093130896911/80000000000000 : ℝ)*(2/5 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1093130896911/80000000000000 : ℝ)*(2/5 : ℝ)=(101093130896911/100000000000000 : ℝ) by norm_num, show 1+2*(284477112228734117/12500000000000000000 : ℝ)=(6534477112228734117/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1093130896911/80000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1093130896911/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1093130896911/80000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1093130896911/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1093130896911/80000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1093130896911/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1854097613/10000000000 : ℝ)*X 0 0+(6026784779/10000000000 : ℝ)*X 0 1+(2397791071/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((688747049/1250000000 : ℝ)*X 1 0+(-511477209/2000000000 : ℝ)*X 1 1+(2397791057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5509976421/10000000000 : ℝ)*X 2 0+(4795582113/10000000000 : ℝ)*X 2 1+(-2557386009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4191377137/10000000000 : ℝ)*X 0 0+(12464487/40000000 : ℝ)*X 0 1+(5623834249/10000000000 : ℝ)*X 0 2+(4191377137/10000000000 : ℝ)*X 1 0+(12464487/40000000 : ℝ)*X 1 1+(5623834249/10000000000 : ℝ)*X 1 2+(4191377137/10000000000 : ℝ)*X 2 0+(12464487/40000000 : ℝ)*X 2 1+(5623834249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1858895661/10000000000 : ℝ)*X 0 0+(603409281/1250000000 : ℝ)*X 0 1+(5993971901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174896653/10000000000 : ℝ)*X 1 0+(-1358993839/10000000000 : ℝ)*X 1 1+(599397433/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587448861/5000000000 : ℝ)*X 2 0+(5993972317/10000000000 : ℝ)*X 2 1+(-679497717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((262572023/625000000 : ℝ)*X 0 0+(5559289711/10000000000 : ℝ)*X 0 1+(3182948901/10000000000 : ℝ)*X 0 2+(262572023/625000000 : ℝ)*X 1 0+(5559289711/10000000000 : ℝ)*X 1 1+(3182948901/10000000000 : ℝ)*X 1 2+(262572023/625000000 : ℝ)*X 2 0+(5559289711/10000000000 : ℝ)*X 2 1+(3182948901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13371200777531954084061/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37555593/50000000000000 : ℝ)*(base1) + (813022677/50000000000000 : ℝ)*(base19) + (1630320227/100000000000000 : ℝ)*(base23) + (184557813/100000000000000 : ℝ)*(upper3) + (97412949/50000000000000 : ℝ)*(upper5) + (605499494363739/100000000000000 : ℝ)*(major0) + (605499494363739/100000000000000 : ℝ)*(major1) + (605499494363739/100000000000000 : ℝ)*(major2) + (203054712103441/25000000000000 : ℝ)*(sp0) + (25381948416211/3125000000000 : ℝ)*(sp1) + (406111172521939/50000000000000 : ℝ)*(sp2) + (398772201998241/100000000000000 : ℝ)*(sp3) + (5202061527/100000000000000 : ℝ)*(sp4) + (157087537/6250000000000 : ℝ)*(sp7) + (199387395255009/50000000000000 : ℝ)*(f.failure) + (406111987682053/50000000000000 : ℝ)*(f.sum) + (18561407265771/4000000000000000000000000000 : ℝ)*base66 + (32491298601771/8000000000000000000000000000 : ℝ)*base68 + (15631740217771/8000000000000000000000000000 : ℝ)*base70 + (70261019745771/8000000000000000000000000000 : ℝ)*base72 + (14386193777771/4000000000000000000000000000 : ℝ)*base74 + (58827311521771/8000000000000000000000000000 : ℝ)*base76 + (15761002577771/8000000000000000000000000000 : ℝ)*base78 + (21043293497771/8000000000000000000000000000 : ℝ)*base80 + (16855264485771/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7875333/5000000000000000000000 : ℝ)*base90 + (7875333/5000000000000000000000 : ℝ)*base92 + (7875333/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29158497770496354037341/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65053571/25000000000000 : ℝ)*(base1) + (101118821/6250000000000 : ℝ)*(base19) + (27912373/1562500000000 : ℝ)*(base23) + (337940389/100000000000000 : ℝ)*(upper3) + (26039211/100000000000000 : ℝ)*(upper5) + (638967193197541/100000000000000 : ℝ)*(major0) + (638967193197541/100000000000000 : ℝ)*(major1) + (638967193197541/100000000000000 : ℝ)*(major2) + (3024195149/100000000000000 : ℝ)*(sp1) + (361486541/12500000000000 : ℝ)*(sp2) + (428559091662249/50000000000000 : ℝ)*(sp4) + (857113281013929/100000000000000 : ℝ)*(sp5) + (428556622413007/50000000000000 : ℝ)*(sp6) + (52601995010387/12500000000000 : ℝ)*(sp7) + (420816220297381/100000000000000 : ℝ)*(f.failure) + (428558961555107/50000000000000 : ℝ)*(f.sum) + (10811457095851/4000000000000000000000000000 : ℝ)*base65 + (104045307615851/8000000000000000000000000000 : ℝ)*base67 + (20259135856149/8000000000000000000000000000 : ℝ)*base70 + (30958742711851/8000000000000000000000000000 : ℝ)*base71 + (29393945215851/4000000000000000000000000000 : ℝ)*base73 + (21249049279851/8000000000000000000000000000 : ℝ)*base75 + (14428053503851/8000000000000000000000000000 : ℝ)*base77 + (23619259631851/8000000000000000000000000000 : ℝ)*base79 + (3667944176149/4000000000000000000000000000 : ℝ)*base82 + (80036903/10000000000000000000000 : ℝ)*base89 + (80036903/10000000000000000000000 : ℝ)*base91 + (80036903/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1263_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13679/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s1_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049977739/10000000000 : ℝ)*x 0 + (5670379949/10000000000 : ℝ)*x 1 + (5026600401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049977739/10000000000 : ℝ)^1057 ≤ (12353323884149/100000000000000 : ℝ)^801 := by
    have hnat : (2049977739 : ℕ)^1057*100000000000000^801 ≤ 12353323884149^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049977739 10000000000 12353323884149 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5670379949/10000000000 : ℝ)^1057 ≤ (23650290948887/50000000000000 : ℝ)^801 := by
    have hnat : (5670379949 : ℕ)^1057*50000000000000^801 ≤ 23650290948887^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670379949 10000000000 23650290948887 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026600401/10000000000 : ℝ)^1057 ≤ (20173047106697/50000000000000 : ℝ)^801 := by
    have hnat : (5026600401 : ℕ)^1057*50000000000000^801 ≤ 20173047106697^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026600401 10000000000 20173047106697 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049977739/10000000000 : ℝ), (5670379949/10000000000 : ℝ), (5026600401/10000000000 : ℝ)] ![(12353323884149/100000000000000 : ℝ), (23650290948887/50000000000000 : ℝ), (20173047106697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049977739/10000000000 : ℝ)|^1057 ≤ (12353323884149/100000000000000 : ℝ)^801
        have hw : |(-2049977739/10000000000 : ℝ)|=(2049977739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5670379949/10000000000 : ℝ)|^1057 ≤ (23650290948887/50000000000000 : ℝ)^801
        have hw : |(5670379949/10000000000 : ℝ)|=(5670379949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026600401/10000000000 : ℝ)|^1057 ≤ (20173047106697/50000000000000 : ℝ)^801
        have hw : |(5026600401/10000000000 : ℝ)|=(5026600401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2706260847/5000000000 : ℝ)*x 0 + (-2395335933/10000000000 : ℝ)*x 1 + (2513300119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706260847/5000000000 : ℝ)^1057 ≤ (8896599509651/20000000000000 : ℝ)^801 := by
    have hnat : (2706260847 : ℕ)^1057*20000000000000^801 ≤ 8896599509651^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706260847 5000000000 8896599509651 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2395335933/10000000000 : ℝ)^1057 ≤ (15170909946827/100000000000000 : ℝ)^801 := by
    have hnat : (2395335933 : ℕ)^1057*100000000000000^801 ≤ 15170909946827^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395335933 10000000000 15170909946827 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513300119/5000000000 : ℝ)^1057 ≤ (40346092486931/100000000000000 : ℝ)^801 := by
    have hnat : (2513300119 : ℕ)^1057*100000000000000^801 ≤ 40346092486931^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513300119 5000000000 40346092486931 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706260847/5000000000 : ℝ), (-2395335933/10000000000 : ℝ), (2513300119/5000000000 : ℝ)] ![(8896599509651/20000000000000 : ℝ), (15170909946827/100000000000000 : ℝ), (40346092486931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706260847/5000000000 : ℝ)|^1057 ≤ (8896599509651/20000000000000 : ℝ)^801
        have hw : |(2706260847/5000000000 : ℝ)|=(2706260847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2395335933/10000000000 : ℝ)|^1057 ≤ (15170909946827/100000000000000 : ℝ)^801
        have hw : |(-2395335933/10000000000 : ℝ)|=(2395335933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2513300119/5000000000 : ℝ)|^1057 ≤ (40346092486931/100000000000000 : ℝ)^801
        have hw : |(2513300119/5000000000 : ℝ)|=(2513300119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2706260761/5000000000 : ℝ)*x 0 + (1005320079/2000000000 : ℝ)*x 1 + (-1197667979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706260761/5000000000 : ℝ)^1057 ≤ (44482995682883/100000000000000 : ℝ)^801 := by
    have hnat : (2706260761 : ℕ)^1057*100000000000000^801 ≤ 44482995682883^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706260761 5000000000 44482995682883 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005320079/2000000000 : ℝ)^1057 ≤ (40346094149843/100000000000000 : ℝ)^801 := by
    have hnat : (1005320079 : ℕ)^1057*100000000000000^801 ≤ 40346094149843^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005320079 2000000000 40346094149843 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197667979/5000000000 : ℝ)^1057 ≤ (1517091015577/10000000000000 : ℝ)^801 := by
    have hnat : (1197667979 : ℕ)^1057*10000000000000^801 ≤ 1517091015577^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197667979 5000000000 1517091015577 10000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706260761/5000000000 : ℝ), (1005320079/2000000000 : ℝ), (-1197667979/5000000000 : ℝ)] ![(44482995682883/100000000000000 : ℝ), (40346094149843/100000000000000 : ℝ), (1517091015577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706260761/5000000000 : ℝ)|^1057 ≤ (44482995682883/100000000000000 : ℝ)^801
        have hw : |(2706260761/5000000000 : ℝ)|=(2706260761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005320079/2000000000 : ℝ)|^1057 ≤ (40346094149843/100000000000000 : ℝ)^801
        have hw : |(1005320079/2000000000 : ℝ)|=(1005320079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197667979/5000000000 : ℝ)|^1057 ≤ (1517091015577/10000000000000 : ℝ)^801
        have hw : |(-1197667979/5000000000 : ℝ)|=(1197667979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1076756289/2500000000 : ℝ)*x 0 + (3699200687/10000000000 : ℝ)*x 1 + (626306303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076756289/2500000000 : ℝ)^1057 ≤ (32904881064831/100000000000000 : ℝ)^801 := by
    have hnat : (1076756289 : ℕ)^1057*100000000000000^801 ≤ 32904881064831^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076756289 2500000000 32904881064831 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3699200687/10000000000 : ℝ)^1057 ≤ (26919994077481/100000000000000 : ℝ)^801 := by
    have hnat : (3699200687 : ℕ)^1057*100000000000000^801 ≤ 26919994077481^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699200687 10000000000 26919994077481 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626306303/1250000000 : ℝ)^1057 ≤ (40175124840193/100000000000000 : ℝ)^801 := by
    have hnat : (626306303 : ℕ)^1057*100000000000000^801 ≤ 40175124840193^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626306303 1250000000 40175124840193 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076756289/2500000000 : ℝ), (3699200687/10000000000 : ℝ), (626306303/1250000000 : ℝ)] ![(32904881064831/100000000000000 : ℝ), (26919994077481/100000000000000 : ℝ), (40175124840193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076756289/2500000000 : ℝ)|^1057 ≤ (32904881064831/100000000000000 : ℝ)^801
        have hw : |(1076756289/2500000000 : ℝ)|=(1076756289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3699200687/10000000000 : ℝ)|^1057 ≤ (26919994077481/100000000000000 : ℝ)^801
        have hw : |(3699200687/10000000000 : ℝ)|=(3699200687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626306303/1250000000 : ℝ)|^1057 ≤ (40175124840193/100000000000000 : ℝ)^801
        have hw : |(626306303/1250000000 : ℝ)|=(626306303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025314891/5000000000 : ℝ)*x 0 + (251749389/500000000 : ℝ)*x 1 + (28309171/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025314891/5000000000 : ℝ)^1057 ≤ (154481365037/1250000000000 : ℝ)^801 := by
    have hnat : (1025314891 : ℕ)^1057*1250000000000^801 ≤ 154481365037^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025314891 5000000000 154481365037 1250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251749389/500000000 : ℝ)^1057 ≤ (40434955299691/100000000000000 : ℝ)^801 := by
    have hnat : (251749389 : ℕ)^1057*100000000000000^801 ≤ 40434955299691^801*500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251749389 500000000 40434955299691 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28309171/50000000 : ℝ)^1057 ≤ (47206535473759/100000000000000 : ℝ)^801 := by
    have hnat : (28309171 : ℕ)^1057*100000000000000^801 ≤ 47206535473759^801*50000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28309171 50000000 47206535473759 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025314891/5000000000 : ℝ), (251749389/500000000 : ℝ), (28309171/50000000 : ℝ)] ![(154481365037/1250000000000 : ℝ), (40434955299691/100000000000000 : ℝ), (47206535473759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025314891/5000000000 : ℝ)|^1057 ≤ (154481365037/1250000000000 : ℝ)^801
        have hw : |(-1025314891/5000000000 : ℝ)|=(1025314891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251749389/500000000 : ℝ)|^1057 ≤ (40434955299691/100000000000000 : ℝ)^801
        have hw : |(251749389/500000000 : ℝ)|=(251749389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28309171/50000000 : ℝ)|^1057 ≤ (47206535473759/100000000000000 : ℝ)^801
        have hw : |(28309171/50000000 : ℝ)|=(28309171/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5246501689/10000000000 : ℝ)*x 0 + (-1760101847/10000000000 : ℝ)*x 1 + (5661834653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246501689/10000000000 : ℝ)^1057 ≤ (8538273582303/20000000000000 : ℝ)^801 := by
    have hnat : (5246501689 : ℕ)^1057*20000000000000^801 ≤ 8538273582303^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246501689 10000000000 8538273582303 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760101847/10000000000 : ℝ)^1057 ≤ (2525522901391/25000000000000 : ℝ)^801 := by
    have hnat : (1760101847 : ℕ)^1057*25000000000000^801 ≤ 2525522901391^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760101847 10000000000 2525522901391 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661834653/10000000000 : ℝ)^1057 ≤ (47206540457847/100000000000000 : ℝ)^801 := by
    have hnat : (5661834653 : ℕ)^1057*100000000000000^801 ≤ 47206540457847^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661834653 10000000000 47206540457847 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246501689/10000000000 : ℝ), (-1760101847/10000000000 : ℝ), (5661834653/10000000000 : ℝ)] ![(8538273582303/20000000000000 : ℝ), (2525522901391/25000000000000 : ℝ), (47206540457847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246501689/10000000000 : ℝ)|^1057 ≤ (8538273582303/20000000000000 : ℝ)^801
        have hw : |(5246501689/10000000000 : ℝ)|=(5246501689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760101847/10000000000 : ℝ)|^1057 ≤ (2525522901391/25000000000000 : ℝ)^801
        have hw : |(-1760101847/10000000000 : ℝ)|=(1760101847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661834653/10000000000 : ℝ)|^1057 ≤ (47206540457847/100000000000000 : ℝ)^801
        have hw : |(5661834653/10000000000 : ℝ)|=(5661834653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2623250803/5000000000 : ℝ)*x 0 + (1132366873/2000000000 : ℝ)*x 1 + (-352020477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623250803/5000000000 : ℝ)^1057 ≤ (21345683510141/50000000000000 : ℝ)^801 := by
    have hnat : (2623250803 : ℕ)^1057*50000000000000^801 ≤ 21345683510141^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623250803 5000000000 21345683510141 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132366873/2000000000 : ℝ)^1057 ≤ (9441307457831/20000000000000 : ℝ)^801 := by
    have hnat : (1132366873 : ℕ)^1057*20000000000000^801 ≤ 9441307457831^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132366873 2000000000 9441307457831 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352020477/2000000000 : ℝ)^1057 ≤ (10102095680289/100000000000000 : ℝ)^801 := by
    have hnat : (352020477 : ℕ)^1057*100000000000000^801 ≤ 10102095680289^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352020477 2000000000 10102095680289 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623250803/5000000000 : ℝ), (1132366873/2000000000 : ℝ), (-352020477/2000000000 : ℝ)] ![(21345683510141/50000000000000 : ℝ), (9441307457831/20000000000000 : ℝ), (10102095680289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623250803/5000000000 : ℝ)|^1057 ≤ (21345683510141/50000000000000 : ℝ)^801
        have hw : |(2623250803/5000000000 : ℝ)|=(2623250803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132366873/2000000000 : ℝ)|^1057 ≤ (9441307457831/20000000000000 : ℝ)^801
        have hw : |(1132366873/2000000000 : ℝ)|=(1132366873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352020477/2000000000 : ℝ)|^1057 ≤ (10102095680289/100000000000000 : ℝ)^801
        have hw : |(-352020477/2000000000 : ℝ)|=(352020477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s1_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (107708819/250000000 : ℝ)*x 0 + (124834179/250000000 : ℝ)*x 1 + (1858303167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107708819/250000000 : ℝ)^1057 ≤ (6583653194197/20000000000000 : ℝ)^801 := by
    have hnat : (107708819 : ℕ)^1057*20000000000000^801 ≤ 6583653194197^801*250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107708819 250000000 6583653194197 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124834179/250000000 : ℝ)^1057 ≤ (7998893391249/20000000000000 : ℝ)^801 := by
    have hnat : (124834179 : ℕ)^1057*20000000000000^801 ≤ 7998893391249^801*250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124834179 250000000 7998893391249 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858303167/5000000000 : ℝ)^1057 ≤ (5417453410813/20000000000000 : ℝ)^801 := by
    have hnat : (1858303167 : ℕ)^1057*20000000000000^801 ≤ 5417453410813^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858303167 5000000000 5417453410813 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107708819/250000000 : ℝ), (124834179/250000000 : ℝ), (1858303167/5000000000 : ℝ)] ![(6583653194197/20000000000000 : ℝ), (7998893391249/20000000000000 : ℝ), (5417453410813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107708819/250000000 : ℝ)|^1057 ≤ (6583653194197/20000000000000 : ℝ)^801
        have hw : |(107708819/250000000 : ℝ)|=(107708819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124834179/250000000 : ℝ)|^1057 ≤ (7998893391249/20000000000000 : ℝ)^801
        have hw : |(124834179/250000000 : ℝ)|=(124834179/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858303167/5000000000 : ℝ)|^1057 ≤ (5417453410813/20000000000000 : ℝ)^801
        have hw : |(1858303167/5000000000 : ℝ)|=(1858303167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13679/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (63/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19911/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13679/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13679/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13679/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13679/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13679/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13679/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (901/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (35995571733/10000000000000000000 : ℝ) := by
    have hpowers : (901/100000 : ℝ)^8455 ≤ (35995571733/10000000000000000000 : ℝ)^2048 := by
      have hnat : (901 : ℕ)^8455*10000000000000000000^2048 ≤ 35995571733^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        901 100000 35995571733 10000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (901/100000 : ℝ)) (X := (35995571733/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13679/50000 : ℝ) ^ (8455/2048 : ℝ) ≤ (23714769086453743/5000000000000000000 : ℝ) := by
    have hpowers : (13679/50000 : ℝ)^8455 ≤ (23714769086453743/5000000000000000000 : ℝ)^2048 := by
      have hnat : (13679 : ℕ)^8455*5000000000000000000^2048 ≤ 23714769086453743^2048*50000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13679 50000 23714769086453743 5000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13679/50000 : ℝ)) (X := (23714769086453743/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000035995571733/5000000000000000000 : ℝ) ≤ (200000000348759/200000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (5000000035995571733/5000000000000000000 : ℝ)^2048 ≤ (200000000348759/200000000000000 : ℝ)^8455 := by
      have hnat : (5000000035995571733 : ℕ)^2048*200000000000000^8455 ≤ 200000000348759^8455*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000035995571733 5000000000000000000 200000000348759 200000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000000348759/200000000000000 : ℝ)) (X := (5000000035995571733/5000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10047429574168479219/10000000000000000000 : ℝ) ≤ (5005733985423523/5000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (10047429574168479219/10000000000000000000 : ℝ)^2048 ≤ (5005733985423523/5000000000000000 : ℝ)^8455 := by
      have hnat : (10047429574168479219 : ℕ)^2048*5000000000000000^8455 ≤ 5005733985423523^8455*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10047429574168479219 10000000000000000000 5005733985423523 5000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005733985423523/5000000000000000 : ℝ)) (X := (10047429574168479219/10000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2523714769086453743/2500000000000000000 : ℝ) ≤ (5011467962128071/5000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (2523714769086453743/2500000000000000000 : ℝ)^2048 ≤ (5011467962128071/5000000000000000 : ℝ)^8455 := by
      have hnat : (2523714769086453743 : ℕ)^2048*5000000000000000^8455 ≤ 5011467962128071^8455*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2523714769086453743 2500000000000000000 5011467962128071 5000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011467962128071/5000000000000000 : ℝ)) (X := (2523714769086453743/2500000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35995571733/10000000000000000000 : ℝ) ≤ ((132274667604656326079/132285000000000000000 : ℝ)+2*(1433494176137/330712500000000 : ℝ)*(901/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (132274667604656326079/132285000000000000000 : ℝ)+2*(1433494176137/330712500000000 : ℝ)*(901/100000 : ℝ)=(200000000348759/200000000000000 : ℝ) by norm_num, show 1+2*(35995571733/10000000000000000000 : ℝ)=(5000000035995571733/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23714769086453743/5000000000000000000 : ℝ)+(35995571733/10000000000000000000 : ℝ) ≤ ((132274667604656326079/132285000000000000000 : ℝ)+(1433494176137/330712500000000 : ℝ)*((13679/50000 : ℝ)+(901/100000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (132274667604656326079/132285000000000000000 : ℝ)+(1433494176137/330712500000000 : ℝ)*((13679/50000 : ℝ)+(901/100000 : ℝ))=(5005733985423523/5000000000000000 : ℝ) by norm_num, show 1+(23714769086453743/5000000000000000000 : ℝ)+(35995571733/10000000000000000000 : ℝ)=(10047429574168479219/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23714769086453743/5000000000000000000 : ℝ) ≤ ((132274667604656326079/132285000000000000000 : ℝ)+2*(1433494176137/330712500000000 : ℝ)*(13679/50000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (132274667604656326079/132285000000000000000 : ℝ)+2*(1433494176137/330712500000000 : ℝ)*(13679/50000 : ℝ)=(5011467962128071/5000000000000000 : ℝ) by norm_num, show 1+2*(23714769086453743/5000000000000000000 : ℝ)=(2523714769086453743/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132274667604656326079/132285000000000000000 : ℝ)*(X 1 0+X 2 0)+(1433494176137/330712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (901/100000 : ℝ)) (hi := (13679/50000 : ℝ)) (c := (132274667604656326079/132285000000000000000 : ℝ)) (alpha := (1433494176137/330712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132274667604656326079/132285000000000000000 : ℝ)*(X 0 1+X 2 1)+(1433494176137/330712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (901/100000 : ℝ)) (hi := (13679/50000 : ℝ)) (c := (132274667604656326079/132285000000000000000 : ℝ)) (alpha := (1433494176137/330712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132274667604656326079/132285000000000000000 : ℝ)*(X 0 2+X 1 2)+(1433494176137/330712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (901/100000 : ℝ)) (hi := (13679/50000 : ℝ)) (c := (132274667604656326079/132285000000000000000 : ℝ)) (alpha := (1433494176137/330712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049977739/10000000000 : ℝ)*X 0 0+(5670379949/10000000000 : ℝ)*X 0 1+(5026600401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706260847/5000000000 : ℝ)*X 1 0+(-2395335933/10000000000 : ℝ)*X 1 1+(2513300119/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706260761/5000000000 : ℝ)*X 2 0+(1005320079/2000000000 : ℝ)*X 2 1+(-1197667979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076756289/2500000000 : ℝ)*X 0 0+(3699200687/10000000000 : ℝ)*X 0 1+(626306303/1250000000 : ℝ)*X 0 2+(1076756289/2500000000 : ℝ)*X 1 0+(3699200687/10000000000 : ℝ)*X 1 1+(626306303/1250000000 : ℝ)*X 1 2+(1076756289/2500000000 : ℝ)*X 2 0+(3699200687/10000000000 : ℝ)*X 2 1+(626306303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1025314891/5000000000 : ℝ)*X 0 0+(251749389/500000000 : ℝ)*X 0 1+(28309171/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246501689/10000000000 : ℝ)*X 1 0+(-1760101847/10000000000 : ℝ)*X 1 1+(5661834653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2623250803/5000000000 : ℝ)*X 2 0+(1132366873/2000000000 : ℝ)*X 2 1+(-352020477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107708819/250000000 : ℝ)*X 0 0+(124834179/250000000 : ℝ)*X 0 1+(1858303167/5000000000 : ℝ)*X 0 2+(107708819/250000000 : ℝ)*X 1 0+(124834179/250000000 : ℝ)*X 1 1+(1858303167/5000000000 : ℝ)*X 1 2+(107708819/250000000 : ℝ)*X 2 0+(124834179/250000000 : ℝ)*X 2 1+(1858303167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1362622553865294375998202939/220475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14159211/20000000000000 : ℝ)*(base1) + (51777959/4000000000000 : ℝ)*(base19) + (622543351/50000000000000 : ℝ)*(base23) + (72539441/50000000000000 : ℝ)*(upper3) + (7702029/6250000000000 : ℝ)*(upper5) + (115798949659659/10000000000000 : ℝ)*(major0) + (115798949659659/10000000000000 : ℝ)*(major1) + (115798949659659/10000000000000 : ℝ)*(major2) + (1553333808300163/100000000000000 : ℝ)*(sp0) + (155333933495133/10000000000000 : ℝ)*(sp1) + (388334846078401/25000000000000 : ℝ)*(sp2) + (762634589171437/100000000000000 : ℝ)*(sp3) + (3445948099/50000000000000 : ℝ)*(sp4) + (699562443/20000000000000 : ℝ)*(sp7) + (190659539444927/25000000000000 : ℝ)*(f.failure) + (776670314700153/50000000000000 : ℝ)*(f.sum) + (96022325453/352760000000000000000000000 : ℝ)*base66 + (3018855089881015687/440950000000000000000000000000000 : ℝ)*base67 + (731740960168234313/440950000000000000000000000000000 : ℝ)*base70 + (593075883637315687/440950000000000000000000000000000 : ℝ)*base71 + (52280352221/14110400000000000000000000 : ℝ)*base73 + (1937823440353615687/440950000000000000000000000000000 : ℝ)*base75 + (1518295134937284313/440950000000000000000000000000000 : ℝ)*base78 + (80725228180665687/440950000000000000000000000000000 : ℝ)*base79 + (168209960739/4409500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6217701/2500000000000000000000 : ℝ)*base89 + (6217701/2500000000000000000000 : ℝ)*base91 + (6217701/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10603298089819495296671684057/1102375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12282979/25000000000000 : ℝ)*(base1) + (1885195177/100000000000000 : ℝ)*(base19) + (1825120341/100000000000000 : ℝ)*(base23) + (250901229/100000000000000 : ℝ)*(upper3) + (105807997/50000000000000 : ℝ)*(upper5) + (594629741520583/50000000000000 : ℝ)*(major0) + (594629741520583/50000000000000 : ℝ)*(major1) + (594629741520583/50000000000000 : ℝ)*(major2) + (9624422017/100000000000000 : ℝ)*(sp1) + (8523510411/100000000000000 : ℝ)*(sp2) + (79764324717963/5000000000000 : ℝ)*(sp4) + (31905498712203/2000000000000 : ℝ)*(sp5) + (99704756037287/6250000000000 : ℝ)*(sp6) + (783232151103253/100000000000000 : ℝ)*(sp7) + (783232200235169/100000000000000 : ℝ)*(f.failure) + (99705402826709/6250000000000 : ℝ)*(f.sum) + (3534325707151/2066953125000000000000000000 : ℝ)*base66 + (514448910603415943/6614250000000000000000000000000000 : ℝ)*base68 + (14578211097466915943/6614250000000000000000000000000000 : ℝ)*base70 + (17187611604012415943/6614250000000000000000000000000000 : ℝ)*base72 + (436294291280771/132285000000000000000000000000 : ℝ)*base73 + (60074170954009915943/6614250000000000000000000000000000 : ℝ)*base76 + (8300981859307084057/6614250000000000000000000000000000 : ℝ)*base77 + (696927000240334057/6614250000000000000000000000000000 : ℝ)*base79 + (147631797098099/33071250000000000000000000000 : ℝ)*base81 + (52258747/10000000000000000000000 : ℝ)*base89 + (52258747/10000000000000000000000 : ℝ)*base91 + (52258747/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1263_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13679/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19911/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1263_s2_0 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-419395847/2000000000 : ℝ)*x 0 + (2744632639/5000000000 : ℝ)*x 1 + (517772201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419395847/2000000000 : ℝ)^1057 ≤ (6364221398121/50000000000000 : ℝ)^801 := by
    have hnat : (419395847 : ℕ)^1057*50000000000000^801 ≤ 6364221398121^801*2000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419395847 2000000000 6364221398121 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744632639/5000000000 : ℝ)^1057 ≤ (5664646938869/12500000000000 : ℝ)^801 := by
    have hnat : (2744632639 : ℕ)^1057*12500000000000^801 ≤ 5664646938869^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744632639 5000000000 5664646938869 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517772201/1000000000 : ℝ)^1057 ≤ (41954381676591/100000000000000 : ℝ)^801 := by
    have hnat : (517772201 : ℕ)^1057*100000000000000^801 ≤ 41954381676591^801*1000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517772201 1000000000 41954381676591 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419395847/2000000000 : ℝ), (2744632639/5000000000 : ℝ), (517772201/1000000000 : ℝ)] ![(6364221398121/50000000000000 : ℝ), (5664646938869/12500000000000 : ℝ), (41954381676591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419395847/2000000000 : ℝ)|^1057 ≤ (6364221398121/50000000000000 : ℝ)^801
        have hw : |(-419395847/2000000000 : ℝ)|=(419395847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744632639/5000000000 : ℝ)|^1057 ≤ (5664646938869/12500000000000 : ℝ)^801
        have hw : |(2744632639/5000000000 : ℝ)|=(2744632639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517772201/1000000000 : ℝ)|^1057 ≤ (41954381676591/100000000000000 : ℝ)^801
        have hw : |(517772201/1000000000 : ℝ)|=(517772201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_1 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368841859/10000000000 : ℝ)*x 0 + (-1129120147/5000000000 : ℝ)*x 1 + (161803819/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368841859/10000000000 : ℝ)^1057 ≤ (22004946897727/50000000000000 : ℝ)^801 := by
    have hnat : (5368841859 : ℕ)^1057*50000000000000^801 ≤ 22004946897727^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368841859 10000000000 22004946897727 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129120147/5000000000 : ℝ)^1057 ≤ (13706760161/97656250000 : ℝ)^801 := by
    have hnat : (1129120147 : ℕ)^1057*97656250000^801 ≤ 13706760161^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129120147 5000000000 13706760161 97656250000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161803819/312500000 : ℝ)^1057 ≤ (8390876758743/20000000000000 : ℝ)^801 := by
    have hnat : (161803819 : ℕ)^1057*20000000000000^801 ≤ 8390876758743^801*312500000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161803819 312500000 8390876758743 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368841859/10000000000 : ℝ), (-1129120147/5000000000 : ℝ), (161803819/312500000 : ℝ)] ![(22004946897727/50000000000000 : ℝ), (13706760161/97656250000 : ℝ), (8390876758743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368841859/10000000000 : ℝ)|^1057 ≤ (22004946897727/50000000000000 : ℝ)^801
        have hw : |(5368841859/10000000000 : ℝ)|=(5368841859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129120147/5000000000 : ℝ)|^1057 ≤ (13706760161/97656250000 : ℝ)^801
        have hw : |(-1129120147/5000000000 : ℝ)|=(1129120147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161803819/312500000 : ℝ)|^1057 ≤ (8390876758743/20000000000000 : ℝ)^801
        have hw : |(161803819/312500000 : ℝ)|=(161803819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_2 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368841791/10000000000 : ℝ)*x 0 + (323607639/625000000 : ℝ)*x 1 + (-1129120181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368841791/10000000000 : ℝ)^1057 ≤ (44009893059889/100000000000000 : ℝ)^801 := by
    have hnat : (5368841791 : ℕ)^1057*100000000000000^801 ≤ 44009893059889^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368841791 10000000000 44009893059889 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323607639/625000000 : ℝ)^1057 ≤ (10488595991199/25000000000000 : ℝ)^801 := by
    have hnat : (323607639 : ℕ)^1057*25000000000000^801 ≤ 10488595991199^801*625000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323607639 625000000 10488595991199 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129120181/5000000000 : ℝ)^1057 ≤ (1754465370323/12500000000000 : ℝ)^801 := by
    have hnat : (1129120181 : ℕ)^1057*12500000000000^801 ≤ 1754465370323^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129120181 5000000000 1754465370323 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368841791/10000000000 : ℝ), (323607639/625000000 : ℝ), (-1129120181/5000000000 : ℝ)] ![(44009893059889/100000000000000 : ℝ), (10488595991199/25000000000000 : ℝ), (1754465370323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368841791/10000000000 : ℝ)|^1057 ≤ (44009893059889/100000000000000 : ℝ)^801
        have hw : |(5368841791/10000000000 : ℝ)|=(5368841791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323607639/625000000 : ℝ)|^1057 ≤ (10488595991199/25000000000000 : ℝ)^801
        have hw : |(323607639/625000000 : ℝ)|=(323607639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129120181/5000000000 : ℝ)|^1057 ≤ (1754465370323/12500000000000 : ℝ)^801
        have hw : |(-1129120181/5000000000 : ℝ)|=(1129120181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_3 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4339535537/10000000000 : ℝ)*x 0 + (2016720783/5000000000 : ℝ)*x 1 + (4667992071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339535537/10000000000 : ℝ)^1057 ≤ (16616514655783/50000000000000 : ℝ)^801 := by
    have hnat : (4339535537 : ℕ)^1057*50000000000000^801 ≤ 16616514655783^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339535537 10000000000 16616514655783 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016720783/5000000000 : ℝ)^1057 ≤ (30175157706819/100000000000000 : ℝ)^801 := by
    have hnat : (2016720783 : ℕ)^1057*100000000000000^801 ≤ 30175157706819^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016720783 5000000000 30175157706819 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4667992071/10000000000 : ℝ)^1057 ≤ (18295906486427/50000000000000 : ℝ)^801 := by
    have hnat : (4667992071 : ℕ)^1057*50000000000000^801 ≤ 18295906486427^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667992071 10000000000 18295906486427 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339535537/10000000000 : ℝ), (2016720783/5000000000 : ℝ), (4667992071/10000000000 : ℝ)] ![(16616514655783/50000000000000 : ℝ), (30175157706819/100000000000000 : ℝ), (18295906486427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339535537/10000000000 : ℝ)|^1057 ≤ (16616514655783/50000000000000 : ℝ)^801
        have hw : |(4339535537/10000000000 : ℝ)|=(4339535537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016720783/5000000000 : ℝ)|^1057 ≤ (30175157706819/100000000000000 : ℝ)^801
        have hw : |(2016720783/5000000000 : ℝ)|=(2016720783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4667992071/10000000000 : ℝ)|^1057 ≤ (18295906486427/50000000000000 : ℝ)^801
        have hw : |(4667992071/10000000000 : ℝ)|=(4667992071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_4 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-209705341/1000000000 : ℝ)*x 0 + (5179696121/10000000000 : ℝ)*x 1 + (5487272919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209705341/1000000000 : ℝ)^1057 ≤ (509161477167/4000000000000 : ℝ)^801 := by
    have hnat : (209705341 : ℕ)^1057*4000000000000^801 ≤ 509161477167^801*1000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209705341 1000000000 509161477167 4000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179696121/10000000000 : ℝ)^1057 ≤ (8395098246453/20000000000000 : ℝ)^801 := by
    have hnat : (5179696121 : ℕ)^1057*20000000000000^801 ≤ 8395098246453^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179696121 10000000000 8395098246453 20000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487272919/10000000000 : ℝ)^1057 ≤ (22647735912677/50000000000000 : ℝ)^801 := by
    have hnat : (5487272919 : ℕ)^1057*50000000000000^801 ≤ 22647735912677^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487272919 10000000000 22647735912677 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209705341/1000000000 : ℝ), (5179696121/10000000000 : ℝ), (5487272919/10000000000 : ℝ)] ![(509161477167/4000000000000 : ℝ), (8395098246453/20000000000000 : ℝ), (22647735912677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209705341/1000000000 : ℝ)|^1057 ≤ (509161477167/4000000000000 : ℝ)^801
        have hw : |(-209705341/1000000000 : ℝ)|=(209705341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179696121/10000000000 : ℝ)|^1057 ≤ (8395098246453/20000000000000 : ℝ)^801
        have hw : |(5179696121/10000000000 : ℝ)|=(5179696121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487272919/10000000000 : ℝ)|^1057 ≤ (22647735912677/50000000000000 : ℝ)^801
        have hw : |(5487272919/10000000000 : ℝ)|=(5487272919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_5 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322294711/2500000000 : ℝ)*x 0 + (-1948689309/10000000000 : ℝ)*x 1 + (5487272963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322294711/2500000000 : ℝ)^1057 ≤ (21575109260213/50000000000000 : ℝ)^801 := by
    have hnat : (1322294711 : ℕ)^1057*50000000000000^801 ≤ 21575109260213^801*2500000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322294711 2500000000 21575109260213 50000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948689309/10000000000 : ℝ)^1057 ≤ (1444288644207/12500000000000 : ℝ)^801 := by
    have hnat : (1948689309 : ℕ)^1057*12500000000000^801 ≤ 1444288644207^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948689309 10000000000 1444288644207 12500000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487272963/10000000000 : ℝ)^1057 ≤ (45295472304639/100000000000000 : ℝ)^801 := by
    have hnat : (5487272963 : ℕ)^1057*100000000000000^801 ≤ 45295472304639^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487272963 10000000000 45295472304639 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322294711/2500000000 : ℝ), (-1948689309/10000000000 : ℝ), (5487272963/10000000000 : ℝ)] ![(21575109260213/50000000000000 : ℝ), (1444288644207/12500000000000 : ℝ), (45295472304639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322294711/2500000000 : ℝ)|^1057 ≤ (21575109260213/50000000000000 : ℝ)^801
        have hw : |(1322294711/2500000000 : ℝ)|=(1322294711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948689309/10000000000 : ℝ)|^1057 ≤ (1444288644207/12500000000000 : ℝ)^801
        have hw : |(-1948689309/10000000000 : ℝ)|=(1948689309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487272963/10000000000 : ℝ)|^1057 ≤ (45295472304639/100000000000000 : ℝ)^801
        have hw : |(5487272963/10000000000 : ℝ)|=(5487272963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_6 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289178967/10000000000 : ℝ)*x 0 + (5487273077/10000000000 : ℝ)*x 1 + (-974344491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289178967/10000000000 : ℝ)^1057 ≤ (2696888740287/6250000000000 : ℝ)^801 := by
    have hnat : (5289178967 : ℕ)^1057*6250000000000^801 ≤ 2696888740287^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289178967 10000000000 2696888740287 6250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487273077/10000000000 : ℝ)^1057 ≤ (45295473546421/100000000000000 : ℝ)^801 := by
    have hnat : (5487273077 : ℕ)^1057*100000000000000^801 ≤ 45295473546421^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487273077 10000000000 45295473546421 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974344491/5000000000 : ℝ)^1057 ≤ (144428832439/1250000000000 : ℝ)^801 := by
    have hnat : (974344491 : ℕ)^1057*1250000000000^801 ≤ 144428832439^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974344491 5000000000 144428832439 1250000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289178967/10000000000 : ℝ), (5487273077/10000000000 : ℝ), (-974344491/5000000000 : ℝ)] ![(2696888740287/6250000000000 : ℝ), (45295473546421/100000000000000 : ℝ), (144428832439/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289178967/10000000000 : ℝ)|^1057 ≤ (2696888740287/6250000000000 : ℝ)^801
        have hw : |(5289178967/10000000000 : ℝ)|=(5289178967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487273077/10000000000 : ℝ)|^1057 ≤ (45295473546421/100000000000000 : ℝ)^801
        have hw : |(5487273077/10000000000 : ℝ)|=(5487273077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974344491/5000000000 : ℝ)|^1057 ≤ (144428832439/1250000000000 : ℝ)^801
        have hw : |(-974344491/5000000000 : ℝ)|=(974344491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1263_s2_7 (p : ℝ) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2169843091/5000000000 : ℝ)*x 0 + (582996463/1250000000 : ℝ)*x 1 + (4037498681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169843091/5000000000 : ℝ)^1057 ≤ (33234551702831/100000000000000 : ℝ)^801 := by
    have hnat : (2169843091 : ℕ)^1057*100000000000000^801 ≤ 33234551702831^801*5000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169843091 5000000000 33234551702831 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582996463/1250000000 : ℝ)^1057 ≤ (9137557819169/25000000000000 : ℝ)^801 := by
    have hnat : (582996463 : ℕ)^1057*25000000000000^801 ≤ 9137557819169^801*1250000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582996463 1250000000 9137557819169 25000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037498681/10000000000 : ℝ)^1057 ≤ (30215217006669/100000000000000 : ℝ)^801 := by
    have hnat : (4037498681 : ℕ)^1057*100000000000000^801 ≤ 30215217006669^801*10000000000^1057 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037498681 10000000000 30215217006669 100000000000000 1057 801 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1057/256 : ℝ)) 1057 801 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169843091/5000000000 : ℝ), (582996463/1250000000 : ℝ), (4037498681/10000000000 : ℝ)] ![(33234551702831/100000000000000 : ℝ), (9137557819169/25000000000000 : ℝ), (30215217006669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169843091/5000000000 : ℝ)|^1057 ≤ (33234551702831/100000000000000 : ℝ)^801
        have hw : |(2169843091/5000000000 : ℝ)|=(2169843091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582996463/1250000000 : ℝ)|^1057 ≤ (9137557819169/25000000000000 : ℝ)^801
        have hw : |(582996463/1250000000 : ℝ)|=(582996463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037498681/10000000000 : ℝ)|^1057 ≤ (30215217006669/100000000000000 : ℝ)^801
        have hw : |(4037498681/10000000000 : ℝ)|=(4037498681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1263_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19911/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (9583/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16169/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19911/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19911/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19911/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19911/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19911/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19911/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/1000 : ℝ) ^ (8455/2048 : ℝ) ≤ (552263008402833/50000000000000000000 : ℝ) := by
    have hpowers : (63/1000 : ℝ)^8455 ≤ (552263008402833/50000000000000000000 : ℝ)^2048 := by
      have hnat : (63 : ℕ)^8455*50000000000000000000^2048 ≤ 552263008402833^2048*1000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 1000 552263008402833 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/1000 : ℝ)) (X := (552263008402833/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19911/100000 : ℝ) ^ (8455/2048 : ℝ) ≤ (63875343678670351/50000000000000000000 : ℝ) := by
    have hpowers : (19911/100000 : ℝ)^8455 ≤ (63875343678670351/50000000000000000000 : ℝ)^2048 := by
      have hnat : (19911 : ℕ)^8455*50000000000000000000^2048 ≤ 63875343678670351^2048*100000^8455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19911 100000 63875343678670351 50000000000000000000 8455 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19911/100000 : ℝ)) (X := (63875343678670351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000552263008402833/25000000000000000000 : ℝ) ≤ (1000005350799171/1000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25000552263008402833/25000000000000000000 : ℝ)^2048 ≤ (1000005350799171/1000000000000000 : ℝ)^8455 := by
      have hnat : (25000552263008402833 : ℕ)^2048*1000000000000000^8455 ≤ 1000005350799171^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000552263008402833 25000000000000000000 1000005350799171 1000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005350799171/1000000000000000 : ℝ)) (X := (25000552263008402833/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1564513362708971037/1562500000000000000 : ℝ) ≤ (250077991347089/250000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (1564513362708971037/1562500000000000000 : ℝ)^2048 ≤ (250077991347089/250000000000000 : ℝ)^8455 := by
      have hnat : (1564513362708971037 : ℕ)^2048*250000000000000^8455 ≤ 250077991347089^8455*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564513362708971037 1562500000000000000 250077991347089 250000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250077991347089/250000000000000 : ℝ)) (X := (1564513362708971037/1562500000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25063875343678670351/25000000000000000000 : ℝ) ≤ (1000618579977541/1000000000000000 : ℝ) ^ (8455/2048 : ℝ) := by
    have hpowers : (25063875343678670351/25000000000000000000 : ℝ)^2048 ≤ (1000618579977541/1000000000000000 : ℝ)^8455 := by
      have hnat : (25063875343678670351 : ℕ)^2048*1000000000000000^8455 ≤ 1000618579977541^8455*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25063875343678670351 25000000000000000000 1000618579977541 1000000000000000 2048 8455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000618579977541/1000000000000000 : ℝ)) (X := (25063875343678670351/25000000000000000000 : ℝ)) (by norm_num) 8455 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(552263008402833/50000000000000000000 : ℝ) ≤ ((4535736495301261827/4537000000000000000 : ℝ)+2*(61322917837/27222000000000 : ℝ)*(63/1000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4535736495301261827/4537000000000000000 : ℝ)+2*(61322917837/27222000000000 : ℝ)*(63/1000 : ℝ)=(1000005350799171/1000000000000000 : ℝ) by norm_num, show 1+2*(552263008402833/50000000000000000000 : ℝ)=(25000552263008402833/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63875343678670351/50000000000000000000 : ℝ)+(552263008402833/50000000000000000000 : ℝ) ≤ ((4535736495301261827/4537000000000000000 : ℝ)+(61322917837/27222000000000 : ℝ)*((19911/100000 : ℝ)+(63/1000 : ℝ)))^(8455/2048 : ℝ) := by
    rw [show (4535736495301261827/4537000000000000000 : ℝ)+(61322917837/27222000000000 : ℝ)*((19911/100000 : ℝ)+(63/1000 : ℝ))=(250077991347089/250000000000000 : ℝ) by norm_num, show 1+(63875343678670351/50000000000000000000 : ℝ)+(552263008402833/50000000000000000000 : ℝ)=(1564513362708971037/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63875343678670351/50000000000000000000 : ℝ) ≤ ((4535736495301261827/4537000000000000000 : ℝ)+2*(61322917837/27222000000000 : ℝ)*(19911/100000 : ℝ))^(8455/2048 : ℝ) := by
    rw [show (4535736495301261827/4537000000000000000 : ℝ)+2*(61322917837/27222000000000 : ℝ)*(19911/100000 : ℝ)=(1000618579977541/1000000000000000 : ℝ) by norm_num, show 1+2*(63875343678670351/50000000000000000000 : ℝ)=(25063875343678670351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4535736495301261827/4537000000000000000 : ℝ)*(X 1 0+X 2 0)+(61322917837/27222000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (63/1000 : ℝ)) (hi := (19911/100000 : ℝ)) (c := (4535736495301261827/4537000000000000000 : ℝ)) (alpha := (61322917837/27222000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4535736495301261827/4537000000000000000 : ℝ)*(X 0 1+X 2 1)+(61322917837/27222000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (63/1000 : ℝ)) (hi := (19911/100000 : ℝ)) (c := (4535736495301261827/4537000000000000000 : ℝ)) (alpha := (61322917837/27222000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4535736495301261827/4537000000000000000 : ℝ)*(X 0 2+X 1 2)+(61322917837/27222000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8455/2048 : ℝ)) (lo := (63/1000 : ℝ)) (hi := (19911/100000 : ℝ)) (c := (4535736495301261827/4537000000000000000 : ℝ)) (alpha := (61322917837/27222000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419395847/2000000000 : ℝ)*X 0 0+(2744632639/5000000000 : ℝ)*X 0 1+(517772201/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368841859/10000000000 : ℝ)*X 1 0+(-1129120147/5000000000 : ℝ)*X 1 1+(161803819/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368841791/10000000000 : ℝ)*X 2 0+(323607639/625000000 : ℝ)*X 2 1+(-1129120181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339535537/10000000000 : ℝ)*X 0 0+(2016720783/5000000000 : ℝ)*X 0 1+(4667992071/10000000000 : ℝ)*X 0 2+(4339535537/10000000000 : ℝ)*X 1 0+(2016720783/5000000000 : ℝ)*X 1 1+(4667992071/10000000000 : ℝ)*X 1 2+(4339535537/10000000000 : ℝ)*X 2 0+(2016720783/5000000000 : ℝ)*X 2 1+(4667992071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-209705341/1000000000 : ℝ)*X 0 0+(5179696121/10000000000 : ℝ)*X 0 1+(5487272919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322294711/2500000000 : ℝ)*X 1 0+(-1948689309/10000000000 : ℝ)*X 1 1+(5487272963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289178967/10000000000 : ℝ)*X 2 0+(5487273077/10000000000 : ℝ)*X 2 1+(-974344491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169843091/5000000000 : ℝ)*X 0 0+(582996463/1250000000 : ℝ)*X 0 1+(4037498681/10000000000 : ℝ)*X 0 2+(2169843091/5000000000 : ℝ)*X 1 0+(582996463/1250000000 : ℝ)*X 1 1+(4037498681/10000000000 : ℝ)*X 1 2+(2169843091/5000000000 : ℝ)*X 2 0+(582996463/1250000000 : ℝ)*X 2 1+(4037498681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1263_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37222874691446015304161409/3544531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (122993711/6250000000000 : ℝ)*(base19) + (1820742813/100000000000000 : ℝ)*(base23) + (57178887/100000000000000 : ℝ)*(lower2) + (292446961/100000000000000 : ℝ)*(upper3) + (73002723/50000000000000 : ℝ)*(upper5) + (149556798228381/6250000000000 : ℝ)*(major0) + (149556798228381/6250000000000 : ℝ)*(major1) + (149556798228381/6250000000000 : ℝ)*(major2) + (160492628758129/5000000000000 : ℝ)*(sp0) + (1604936934744701/50000000000000 : ℝ)*(sp1) + (641974803329193/20000000000000 : ℝ)*(sp2) + (1575929225210701/100000000000000 : ℝ)*(sp3) + (23262226197/100000000000000 : ℝ)*(sp4) + (6065329449/50000000000000 : ℝ)*(sp7) + (787970677934799/50000000000000 : ℝ)*(f.failure) + (1604937918694389/50000000000000 : ℝ)*(f.sum) + (24318725315371/4537000000000000000000000000 : ℝ)*base66 + (119826364688406663/28356250000000000000000000000000 : ℝ)*base68 + (102316182575162087/28356250000000000000000000000000 : ℝ)*base69 + (104687194086981663/28356250000000000000000000000000 : ℝ)*base72 + (393632325213/90740000000000000000000000 : ℝ)*base74 + (14261884206719163/28356250000000000000000000000000 : ℝ)*base76 + (448621426283162913/28356250000000000000000000000000 : ℝ)*base78 + (24902600214274587/28356250000000000000000000000000 : ℝ)*base79 + (2940000901117/4537000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3427563/5000000000000000000000 : ℝ)*base90 + (3427563/5000000000000000000000 : ℝ)*base92 + (3427563/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (780565461238699348898171269/226850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1084230679/100000000000000 : ℝ)*(base19) + (1374131187/100000000000000 : ℝ)*(base23) + (6176289/10000000000000 : ℝ)*(upper2) + (165560977/100000000000000 : ℝ)*(upper3) + (15648429/25000000000000 : ℝ)*(upper5) + (2423728662555583/100000000000000 : ℝ)*(major0) + (2423728662555583/100000000000000 : ℝ)*(major1) + (2423728662555583/100000000000000 : ℝ)*(major2) + (21328041/195312500000 : ℝ)*(sp1) + (1739486101/10000000000000 : ℝ)*(sp2) + (812804559919977/25000000000000 : ℝ)*(sp4) + (3251206235492237/100000000000000 : ℝ)*(sp5) + (3251199470687711/100000000000000 : ℝ)*(sp6) + (798119485367493/50000000000000 : ℝ)*(sp7) + (798119485367493/50000000000000 : ℝ)*(f.failure) + (812804559919977/25000000000000 : ℝ)*(f.sum) + (1285372875809/6805500000000000000000000000 : ℝ)*base65 + (1313891550376809577/1361100000000000000000000000000000 : ℝ)*base68 + (2800746173633409577/1361100000000000000000000000000000 : ℝ)*base70 + (8353164008792409577/1361100000000000000000000000000000 : ℝ)*base72 + (11244640094017/13611000000000000000000000000 : ℝ)*base73 + (3580595380659909577/1361100000000000000000000000000000 : ℝ)*base76 + (424867153972509577/1361100000000000000000000000000000 : ℝ)*base78 + (7253604168947709577/1361100000000000000000000000000000 : ℝ)*base80 + (14208644131387/6805500000000000000000000000 : ℝ)*base82 + (28522759/5000000000000000000000 : ℝ)*base89 + (28522759/5000000000000000000000 : ℝ)*base91 + (28522759/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1263_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19911/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1263_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1263_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1263_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1263_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1263_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8455/2048 : ℝ) ≤ p) (hpb : p ≤ (1057/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151839963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1263_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
