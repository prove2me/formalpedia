-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:14.937428+00:00
-- url     : https://prove2.me/submissions/a33463cb-50f4-4ffc-848b-5ef10f70ce36

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
theorem support_rectangle_w1271_s0_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851338431/10000000000 : ℝ)*x 0 + (6024769477/10000000000 : ℝ)*x 1 + (4796690303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851338431/10000000000 : ℝ)^8465 ≤ (675433011411/6250000000000 : ℝ)^6417 := by
    have hnat : (1851338431 : ℕ)^8465*6250000000000^6417 ≤ 675433011411^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851338431 10000000000 675433011411 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024769477/10000000000 : ℝ)^8465 ≤ (51251659060207/100000000000000 : ℝ)^6417 := by
    have hnat : (6024769477 : ℕ)^8465*100000000000000^6417 ≤ 51251659060207^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024769477 10000000000 51251659060207 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796690303/10000000000 : ℝ)^8465 ≤ (7588282548479/20000000000000 : ℝ)^6417 := by
    have hnat : (4796690303 : ℕ)^8465*20000000000000^6417 ≤ 7588282548479^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796690303 10000000000 7588282548479 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851338431/10000000000 : ℝ), (6024769477/10000000000 : ℝ), (4796690303/10000000000 : ℝ)] ![(675433011411/6250000000000 : ℝ), (51251659060207/100000000000000 : ℝ), (7588282548479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851338431/10000000000 : ℝ)|^8465 ≤ (675433011411/6250000000000 : ℝ)^6417
        have hw : |(-1851338431/10000000000 : ℝ)|=(1851338431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024769477/10000000000 : ℝ)|^8465 ≤ (51251659060207/100000000000000 : ℝ)^6417
        have hw : |(6024769477/10000000000 : ℝ)|=(6024769477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796690303/10000000000 : ℝ)|^8465 ≤ (7588282548479/20000000000000 : ℝ)^6417
        have hw : |(4796690303/10000000000 : ℝ)|=(4796690303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5509469469/10000000000 : ℝ)*x 0 + (-159537769/625000000 : ℝ)*x 1 + (1199172569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509469469/10000000000 : ℝ)^8465 ≤ (22774790391801/50000000000000 : ℝ)^6417 := by
    have hnat : (5509469469 : ℕ)^8465*50000000000000^6417 ≤ 22774790391801^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509469469 10000000000 22774790391801 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159537769/625000000 : ℝ)^8465 ≤ (16509006743353/100000000000000 : ℝ)^6417 := by
    have hnat : (159537769 : ℕ)^8465*100000000000000^6417 ≤ 16509006743353^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159537769 625000000 16509006743353 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199172569/2500000000 : ℝ)^8465 ≤ (37941412460667/100000000000000 : ℝ)^6417 := by
    have hnat : (1199172569 : ℕ)^8465*100000000000000^6417 ≤ 37941412460667^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199172569 2500000000 37941412460667 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509469469/10000000000 : ℝ), (-159537769/625000000 : ℝ), (1199172569/2500000000 : ℝ)] ![(22774790391801/50000000000000 : ℝ), (16509006743353/100000000000000 : ℝ), (37941412460667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509469469/10000000000 : ℝ)|^8465 ≤ (22774790391801/50000000000000 : ℝ)^6417
        have hw : |(5509469469/10000000000 : ℝ)|=(5509469469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159537769/625000000 : ℝ)|^8465 ≤ (16509006743353/100000000000000 : ℝ)^6417
        have hw : |(-159537769/625000000 : ℝ)|=(159537769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199172569/2500000000 : ℝ)|^8465 ≤ (37941412460667/100000000000000 : ℝ)^6417
        have hw : |(1199172569/2500000000 : ℝ)|=(1199172569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2754734743/5000000000 : ℝ)*x 0 + (4796690277/10000000000 : ℝ)*x 1 + (-63815107/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754734743/5000000000 : ℝ)^8465 ≤ (22774790484503/50000000000000 : ℝ)^6417 := by
    have hnat : (2754734743 : ℕ)^8465*50000000000000^6417 ≤ 22774790484503^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754734743 5000000000 22774790484503 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4796690277/10000000000 : ℝ)^8465 ≤ (37941412471101/100000000000000 : ℝ)^6417 := by
    have hnat : (4796690277 : ℕ)^8465*100000000000000^6417 ≤ 37941412471101^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796690277 10000000000 37941412471101 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63815107/250000000 : ℝ)^8465 ≤ (8254503269297/50000000000000 : ℝ)^6417 := by
    have hnat : (63815107 : ℕ)^8465*50000000000000^6417 ≤ 8254503269297^6417*250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63815107 250000000 8254503269297 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754734743/5000000000 : ℝ), (4796690277/10000000000 : ℝ), (-63815107/250000000 : ℝ)] ![(22774790484503/50000000000000 : ℝ), (37941412471101/100000000000000 : ℝ), (8254503269297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754734743/5000000000 : ℝ)|^8465 ≤ (22774790484503/50000000000000 : ℝ)^6417
        have hw : |(2754734743/5000000000 : ℝ)|=(2754734743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4796690277/10000000000 : ℝ)|^8465 ≤ (37941412471101/100000000000000 : ℝ)^6417
        have hw : |(4796690277/10000000000 : ℝ)|=(4796690277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63815107/250000000 : ℝ)|^8465 ≤ (8254503269297/50000000000000 : ℝ)^6417
        have hw : |(-63815107/250000000 : ℝ)|=(63815107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4190675313/10000000000 : ℝ)*x 0 + (1557901697/5000000000 : ℝ)*x 1 + (562148733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190675313/10000000000 : ℝ)^8465 ≤ (634987391291/2000000000000 : ℝ)^6417 := by
    have hnat : (4190675313 : ℕ)^8465*2000000000000^6417 ≤ 634987391291^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190675313 10000000000 634987391291 2000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557901697/5000000000 : ℝ)^8465 ≤ (21475425917209/100000000000000 : ℝ)^6417 := by
    have hnat : (1557901697 : ℕ)^8465*100000000000000^6417 ≤ 21475425917209^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557901697 5000000000 21475425917209 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562148733/1000000000 : ℝ)^8465 ≤ (46775204499423/100000000000000 : ℝ)^6417 := by
    have hnat : (562148733 : ℕ)^8465*100000000000000^6417 ≤ 46775204499423^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562148733 1000000000 46775204499423 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190675313/10000000000 : ℝ), (1557901697/5000000000 : ℝ), (562148733/1000000000 : ℝ)] ![(634987391291/2000000000000 : ℝ), (21475425917209/100000000000000 : ℝ), (46775204499423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190675313/10000000000 : ℝ)|^8465 ≤ (634987391291/2000000000000 : ℝ)^6417
        have hw : |(4190675313/10000000000 : ℝ)|=(4190675313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1557901697/5000000000 : ℝ)|^8465 ≤ (21475425917209/100000000000000 : ℝ)^6417
        have hw : |(1557901697/5000000000 : ℝ)|=(1557901697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562148733/1000000000 : ℝ)|^8465 ≤ (46775204499423/100000000000000 : ℝ)^6417
        have hw : |(562148733/1000000000 : ℝ)|=(562148733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-928055607/5000000000 : ℝ)*x 0 + (4828295761/10000000000 : ℝ)*x 1 + (2996023027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928055607/5000000000 : ℝ)^8465 ≤ (2710923867379/25000000000000 : ℝ)^6417 := by
    have hnat : (928055607 : ℕ)^8465*25000000000000^6417 ≤ 2710923867379^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928055607 5000000000 2710923867379 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4828295761/10000000000 : ℝ)^8465 ≤ (7654308481031/20000000000000 : ℝ)^6417 := by
    have hnat : (4828295761 : ℕ)^8465*20000000000000^6417 ≤ 7654308481031^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828295761 10000000000 7654308481031 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996023027/5000000000 : ℝ)^8465 ≤ (50884762114229/100000000000000 : ℝ)^6417 := by
    have hnat : (2996023027 : ℕ)^8465*100000000000000^6417 ≤ 50884762114229^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996023027 5000000000 50884762114229 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928055607/5000000000 : ℝ), (4828295761/10000000000 : ℝ), (2996023027/5000000000 : ℝ)] ![(2710923867379/25000000000000 : ℝ), (7654308481031/20000000000000 : ℝ), (50884762114229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928055607/5000000000 : ℝ)|^8465 ≤ (2710923867379/25000000000000 : ℝ)^6417
        have hw : |(-928055607/5000000000 : ℝ)|=(928055607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4828295761/10000000000 : ℝ)|^8465 ≤ (7654308481031/20000000000000 : ℝ)^6417
        have hw : |(4828295761/10000000000 : ℝ)|=(4828295761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996023027/5000000000 : ℝ)|^8465 ≤ (50884762114229/100000000000000 : ℝ)^6417
        have hw : |(2996023027/5000000000 : ℝ)|=(2996023027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5175203377/10000000000 : ℝ)*x 0 + (-1357246057/10000000000 : ℝ)*x 1 + (2996024271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175203377/10000000000 : ℝ)^8465 ≤ (41939834651291/100000000000000 : ℝ)^6417 := by
    have hnat : (5175203377 : ℕ)^8465*100000000000000^6417 ≤ 41939834651291^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175203377 10000000000 41939834651291 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357246057/10000000000 : ℝ)^8465 ≤ (3587687673211/50000000000000 : ℝ)^6417 := by
    have hnat : (1357246057 : ℕ)^8465*50000000000000^6417 ≤ 3587687673211^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357246057 10000000000 3587687673211 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996024271/5000000000 : ℝ)^8465 ≤ (25442394992787/50000000000000 : ℝ)^6417 := by
    have hnat : (2996024271 : ℕ)^8465*50000000000000^6417 ≤ 25442394992787^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996024271 5000000000 25442394992787 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175203377/10000000000 : ℝ), (-1357246057/10000000000 : ℝ), (2996024271/5000000000 : ℝ)] ![(41939834651291/100000000000000 : ℝ), (3587687673211/50000000000000 : ℝ), (25442394992787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175203377/10000000000 : ℝ)|^8465 ≤ (41939834651291/100000000000000 : ℝ)^6417
        have hw : |(5175203377/10000000000 : ℝ)|=(5175203377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1357246057/10000000000 : ℝ)|^8465 ≤ (3587687673211/50000000000000 : ℝ)^6417
        have hw : |(-1357246057/10000000000 : ℝ)|=(1357246057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996024271/5000000000 : ℝ)|^8465 ≤ (25442394992787/50000000000000 : ℝ)^6417
        have hw : |(2996024271/5000000000 : ℝ)|=(2996024271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587602253/5000000000 : ℝ)*x 0 + (2996023233/5000000000 : ℝ)*x 1 + (-1357247663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587602253/5000000000 : ℝ)^8465 ≤ (1048496168019/2500000000000 : ℝ)^6417 := by
    have hnat : (2587602253 : ℕ)^8465*2500000000000^6417 ≤ 1048496168019^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587602253 5000000000 1048496168019 2500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2996023233/5000000000 : ℝ)^8465 ≤ (2544238336479/5000000000000 : ℝ)^6417 := by
    have hnat : (2996023233 : ℕ)^8465*5000000000000^6417 ≤ 2544238336479^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996023233 5000000000 2544238336479 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357247663/10000000000 : ℝ)^8465 ≤ (3587693273321/50000000000000 : ℝ)^6417 := by
    have hnat : (1357247663 : ℕ)^8465*50000000000000^6417 ≤ 3587693273321^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357247663 10000000000 3587693273321 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587602253/5000000000 : ℝ), (2996023233/5000000000 : ℝ), (-1357247663/10000000000 : ℝ)] ![(1048496168019/2500000000000 : ℝ), (2544238336479/5000000000000 : ℝ), (3587693273321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587602253/5000000000 : ℝ)|^8465 ≤ (1048496168019/2500000000000 : ℝ)^6417
        have hw : |(2587602253/5000000000 : ℝ)|=(2587602253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2996023233/5000000000 : ℝ)|^8465 ≤ (2544238336479/5000000000000 : ℝ)^6417
        have hw : |(2996023233/5000000000 : ℝ)|=(2996023233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1357247663/10000000000 : ℝ)|^8465 ≤ (3587693273321/50000000000000 : ℝ)^6417
        have hw : |(-1357247663/10000000000 : ℝ)|=(1357247663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s0_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168016661/400000000 : ℝ)*x 0 + (694626007/1250000000 : ℝ)*x 1 + (795640901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168016661/400000000 : ℝ)^8465 ≤ (6369352165181/20000000000000 : ℝ)^6417 := by
    have hnat : (168016661 : ℕ)^8465*20000000000000^6417 ≤ 6369352165181^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168016661 400000000 6369352165181 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694626007/1250000000 : ℝ)^8465 ≤ (5758594238411/12500000000000 : ℝ)^6417 := by
    have hnat : (694626007 : ℕ)^8465*12500000000000^6417 ≤ 5758594238411^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694626007 1250000000 5758594238411 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795640901/2500000000 : ℝ)^8465 ≤ (4416897049713/20000000000000 : ℝ)^6417 := by
    have hnat : (795640901 : ℕ)^8465*20000000000000^6417 ≤ 4416897049713^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795640901 2500000000 4416897049713 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168016661/400000000 : ℝ), (694626007/1250000000 : ℝ), (795640901/2500000000 : ℝ)] ![(6369352165181/20000000000000 : ℝ), (5758594238411/12500000000000 : ℝ), (4416897049713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168016661/400000000 : ℝ)|^8465 ≤ (6369352165181/20000000000000 : ℝ)^6417
        have hw : |(168016661/400000000 : ℝ)|=(168016661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(694626007/1250000000 : ℝ)|^8465 ≤ (5758594238411/12500000000000 : ℝ)^6417
        have hw : |(694626007/1250000000 : ℝ)|=(694626007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795640901/2500000000 : ℝ)|^8465 ≤ (4416897049713/20000000000000 : ℝ)^6417
        have hw : |(795640901/2500000000 : ℝ)|=(795640901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (937/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6831/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (529/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^529 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^529*1^128 ≤ 0^128*1^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (529/128 : ℝ) ≤ (1133335681772981199/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^529 ≤ (1133335681772981199/50000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^529*50000000000000000000^128 ≤ 1133335681772981199^128*5^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1133335681772981199 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1133335681772981199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^529 := by
      have hnat : (1 : ℕ)^128*1^529 ≤ 1^529*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (51133335681772981199/50000000000000000000 : ℝ) ≤ (314199397290519/312500000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (51133335681772981199/50000000000000000000 : ℝ)^128 ≤ (314199397290519/312500000000000 : ℝ)^529 := by
      have hnat : (51133335681772981199 : ℕ)^128*312500000000000^529 ≤ 314199397290519^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51133335681772981199 50000000000000000000 314199397290519 312500000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314199397290519/312500000000000 : ℝ)) (X := (51133335681772981199/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (26133335681772981199/25000000000000000000 : ℝ) ≤ (157949397290519/156250000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (26133335681772981199/25000000000000000000 : ℝ)^128 ≤ (157949397290519/156250000000000 : ℝ)^529 := by
      have hnat : (26133335681772981199 : ℕ)^128*156250000000000^529 ≤ 157949397290519^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26133335681772981199 25000000000000000000 157949397290519 156250000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157949397290519/156250000000000 : ℝ)) (X := (26133335681772981199/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1699397290519/125000000000000 : ℝ)*(0 : ℝ))^(529/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(1699397290519/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1133335681772981199/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1699397290519/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(529/128 : ℝ) := by
    rw [show (1 : ℝ)+(1699397290519/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(314199397290519/312500000000000 : ℝ) by norm_num, show 1+(1133335681772981199/50000000000000000000 : ℝ)+(0 : ℝ)=(51133335681772981199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1133335681772981199/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1699397290519/125000000000000 : ℝ)*(2/5 : ℝ))^(529/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(1699397290519/125000000000000 : ℝ)*(2/5 : ℝ)=(157949397290519/156250000000000 : ℝ) by norm_num, show 1+2*(1133335681772981199/50000000000000000000 : ℝ)=(26133335681772981199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1699397290519/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1699397290519/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1699397290519/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1699397290519/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1699397290519/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1699397290519/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1851338431/10000000000 : ℝ)*X 0 0+(6024769477/10000000000 : ℝ)*X 0 1+(4796690303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5509469469/10000000000 : ℝ)*X 1 0+(-159537769/625000000 : ℝ)*X 1 1+(1199172569/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754734743/5000000000 : ℝ)*X 2 0+(4796690277/10000000000 : ℝ)*X 2 1+(-63815107/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4190675313/10000000000 : ℝ)*X 0 0+(1557901697/5000000000 : ℝ)*X 0 1+(562148733/1000000000 : ℝ)*X 0 2+(4190675313/10000000000 : ℝ)*X 1 0+(1557901697/5000000000 : ℝ)*X 1 1+(562148733/1000000000 : ℝ)*X 1 2+(4190675313/10000000000 : ℝ)*X 2 0+(1557901697/5000000000 : ℝ)*X 2 1+(562148733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-928055607/5000000000 : ℝ)*X 0 0+(4828295761/10000000000 : ℝ)*X 0 1+(2996023027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175203377/10000000000 : ℝ)*X 1 0+(-1357246057/10000000000 : ℝ)*X 1 1+(2996024271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587602253/5000000000 : ℝ)*X 2 0+(2996023233/5000000000 : ℝ)*X 2 1+(-1357247663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168016661/400000000 : ℝ)*X 0 0+(694626007/1250000000 : ℝ)*X 0 1+(795640901/2500000000 : ℝ)*X 0 2+(168016661/400000000 : ℝ)*X 1 0+(694626007/1250000000 : ℝ)*X 1 1+(795640901/2500000000 : ℝ)*X 1 2+(168016661/400000000 : ℝ)*X 2 0+(694626007/1250000000 : ℝ)*X 2 1+(795640901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4089876919767470234073/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9972067/25000000000000 : ℝ)*(base1) + (399182297/50000000000000 : ℝ)*(base19) + (160175429/20000000000000 : ℝ)*(base23) + (897743/1000000000000 : ℝ)*(upper3) + (19283001/20000000000000 : ℝ)*(upper5) + (606689894802161/100000000000000 : ℝ)*(major0) + (606689894802161/100000000000000 : ℝ)*(major1) + (606689894802161/100000000000000 : ℝ)*(major2) + (162856423473409/20000000000000 : ℝ)*(sp0) + (814283824865011/100000000000000 : ℝ)*(sp1) + (40714191117623/5000000000000 : ℝ)*(sp2) + (39909380154441/10000000000000 : ℝ)*(sp3) + (636437707/25000000000000 : ℝ)*(sp4) + (1215878649/100000000000000 : ℝ)*(sp7) + (12471720540979/3125000000000 : ℝ)*(f.failure) + (162856924645921/20000000000000 : ℝ)*(f.sum) + (5342236836559/6250000000000000000000000000 : ℝ)*base65 + (68951827799059/12500000000000000000000000000 : ℝ)*base67 + (93753525474059/12500000000000000000000000000 : ℝ)*base69 + (36229018336559/12500000000000000000000000000 : ℝ)*base71 + (28085467636559/6250000000000000000000000000 : ℝ)*base73 + (21851920638441/12500000000000000000000000000 : ℝ)*base76 + (11776688324059/12500000000000000000000000000 : ℝ)*base77 + (13543004711559/12500000000000000000000000000 : ℝ)*base79 + (40976899161559/6250000000000000000000000000 : ℝ)*base81 + (979831/312500000000000000000 : ℝ)*base89 + (979831/312500000000000000000 : ℝ)*base91 + (979831/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5162795520085972602039/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (260151749/100000000000000 : ℝ)*(base1) + (61750443/10000000000000 : ℝ)*(base19) + (189770673/25000000000000 : ℝ)*(base23) + (58841633/50000000000000 : ℝ)*(upper3) + (640221476503777/100000000000000 : ℝ)*(major0) + (640221476503777/100000000000000 : ℝ)*(major1) + (640221476503777/100000000000000 : ℝ)*(major2) + (785190187/50000000000000 : ℝ)*(sp1) + (430023749/50000000000000 : ℝ)*(sp2) + (285087387/50000000000000 : ℝ)*(sp3) + (429645086460467/50000000000000 : ℝ)*(sp4) + (859287724884381/100000000000000 : ℝ)*(sp5) + (171857658727799/20000000000000 : ℝ)*(sp6) + (421152099772203/100000000000000 : ℝ)*(sp7) + (210576465049363/50000000000000 : ℝ)*(f.failure) + (26852809774037/3125000000000 : ℝ)*(f.sum) + (1377973715987/6250000000000000000000000000 : ℝ)*base66 + (63477768934737/12500000000000000000000000000 : ℝ)*base68 + (9170223559737/12500000000000000000000000000 : ℝ)*base70 + (38614691209737/12500000000000000000000000000 : ℝ)*base72 + (3717535903487/6250000000000000000000000000 : ℝ)*base74 + (29769864684737/12500000000000000000000000000 : ℝ)*base76 + (89207209397237/12500000000000000000000000000 : ℝ)*base78 + (51777241959737/12500000000000000000000000000 : ℝ)*base80 + (31268601621513/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20010207/5000000000000000000000 : ℝ)*base89 + (20010207/5000000000000000000000 : ℝ)*base91 + (20010207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1271_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s1_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046567799/10000000000 : ℝ)*x 0 + (5668142889/10000000000 : ℝ)*x 1 + (5028346023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046567799/10000000000 : ℝ)^8465 ≤ (154187295079/1250000000000 : ℝ)^6417 := by
    have hnat : (2046567799 : ℕ)^8465*1250000000000^6417 ≤ 154187295079^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046567799 10000000000 154187295079 1250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5668142889/10000000000 : ℝ)^8465 ≤ (1891519636109/4000000000000 : ℝ)^6417 := by
    have hnat : (5668142889 : ℕ)^8465*4000000000000^6417 ≤ 1891519636109^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668142889 10000000000 1891519636109 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028346023/10000000000 : ℝ)^8465 ≤ (20188512740547/50000000000000 : ℝ)^6417 := by
    have hnat : (5028346023 : ℕ)^8465*50000000000000^6417 ≤ 20188512740547^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028346023 10000000000 20188512740547 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046567799/10000000000 : ℝ), (5668142889/10000000000 : ℝ), (5028346023/10000000000 : ℝ)] ![(154187295079/1250000000000 : ℝ), (1891519636109/4000000000000 : ℝ), (20188512740547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046567799/10000000000 : ℝ)|^8465 ≤ (154187295079/1250000000000 : ℝ)^6417
        have hw : |(-2046567799/10000000000 : ℝ)|=(2046567799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5668142889/10000000000 : ℝ)|^8465 ≤ (1891519636109/4000000000000 : ℝ)^6417
        have hw : |(5668142889/10000000000 : ℝ)|=(5668142889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028346023/10000000000 : ℝ)|^8465 ≤ (20188512740547/50000000000000 : ℝ)^6417
        have hw : |(5028346023/10000000000 : ℝ)|=(5028346023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706015629/5000000000 : ℝ)*x 0 + (-477928529/2000000000 : ℝ)*x 1 + (628543271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706015629/5000000000 : ℝ)^8465 ≤ (44489920980763/100000000000000 : ℝ)^6417 := by
    have hnat : (2706015629 : ℕ)^8465*100000000000000^6417 ≤ 44489920980763^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706015629 5000000000 44489920980763 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477928529/2000000000 : ℝ)^8465 ≤ (1513305199573/10000000000000 : ℝ)^6417 := by
    have hnat : (477928529 : ℕ)^8465*10000000000000^6417 ≤ 1513305199573^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477928529 2000000000 1513305199573 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628543271/1250000000 : ℝ)^8465 ≤ (40377027017027/100000000000000 : ℝ)^6417 := by
    have hnat : (628543271 : ℕ)^8465*100000000000000^6417 ≤ 40377027017027^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628543271 1250000000 40377027017027 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706015629/5000000000 : ℝ), (-477928529/2000000000 : ℝ), (628543271/1250000000 : ℝ)] ![(44489920980763/100000000000000 : ℝ), (1513305199573/10000000000000 : ℝ), (40377027017027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706015629/5000000000 : ℝ)|^8465 ≤ (44489920980763/100000000000000 : ℝ)^6417
        have hw : |(2706015629/5000000000 : ℝ)|=(2706015629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477928529/2000000000 : ℝ)|^8465 ≤ (1513305199573/10000000000000 : ℝ)^6417
        have hw : |(-477928529/2000000000 : ℝ)|=(477928529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628543271/1250000000 : ℝ)|^8465 ≤ (40377027017027/100000000000000 : ℝ)^6417
        have hw : |(628543271/1250000000 : ℝ)|=(628543271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5412031383/10000000000 : ℝ)*x 0 + (314271631/625000000 : ℝ)*x 1 + (-2389642573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412031383/10000000000 : ℝ)^8465 ≤ (11122480584071/25000000000000 : ℝ)^6417 := by
    have hnat : (5412031383 : ℕ)^8465*25000000000000^6417 ≤ 11122480584071^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412031383 10000000000 11122480584071 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314271631/625000000 : ℝ)^8465 ≤ (40377026254357/100000000000000 : ℝ)^6417 := by
    have hnat : (314271631 : ℕ)^8465*100000000000000^6417 ≤ 40377026254357^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314271631 625000000 40377026254357 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389642573/10000000000 : ℝ)^8465 ≤ (60532205577/400000000000 : ℝ)^6417 := by
    have hnat : (2389642573 : ℕ)^8465*400000000000^6417 ≤ 60532205577^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389642573 10000000000 60532205577 400000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412031383/10000000000 : ℝ), (314271631/625000000 : ℝ), (-2389642573/10000000000 : ℝ)] ![(11122480584071/25000000000000 : ℝ), (40377026254357/100000000000000 : ℝ), (60532205577/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412031383/10000000000 : ℝ)|^8465 ≤ (11122480584071/25000000000000 : ℝ)^6417
        have hw : |(5412031383/10000000000 : ℝ)|=(5412031383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314271631/625000000 : ℝ)|^8465 ≤ (40377026254357/100000000000000 : ℝ)^6417
        have hw : |(314271631/625000000 : ℝ)|=(314271631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2389642573/10000000000 : ℝ)|^8465 ≤ (60532205577/400000000000 : ℝ)^6417
        have hw : |(-2389642573/10000000000 : ℝ)|=(2389642573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2153121497/5000000000 : ℝ)*x 0 + (740166541/2000000000 : ℝ)*x 1 + (1001245677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153121497/5000000000 : ℝ)^8465 ≤ (32909422056577/100000000000000 : ℝ)^6417 := by
    have hnat : (2153121497 : ℕ)^8465*100000000000000^6417 ≤ 32909422056577^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153121497 5000000000 32909422056577 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740166541/2000000000 : ℝ)^8465 ≤ (13473835976099/50000000000000 : ℝ)^6417 := by
    have hnat : (740166541 : ℕ)^8465*50000000000000^6417 ≤ 13473835976099^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740166541 2000000000 13473835976099 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001245677/2000000000 : ℝ)^8465 ≤ (501786324769/1250000000000 : ℝ)^6417 := by
    have hnat : (1001245677 : ℕ)^8465*1250000000000^6417 ≤ 501786324769^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001245677 2000000000 501786324769 1250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153121497/5000000000 : ℝ), (740166541/2000000000 : ℝ), (1001245677/2000000000 : ℝ)] ![(32909422056577/100000000000000 : ℝ), (13473835976099/50000000000000 : ℝ), (501786324769/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153121497/5000000000 : ℝ)|^8465 ≤ (32909422056577/100000000000000 : ℝ)^6417
        have hw : |(2153121497/5000000000 : ℝ)|=(2153121497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740166541/2000000000 : ℝ)|^8465 ≤ (13473835976099/50000000000000 : ℝ)^6417
        have hw : |(740166541/2000000000 : ℝ)|=(740166541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001245677/2000000000 : ℝ)|^8465 ≤ (501786324769/1250000000000 : ℝ)^6417
        have hw : |(1001245677/2000000000 : ℝ)|=(1001245677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047209433/10000000000 : ℝ)*x 0 + (5036651781/10000000000 : ℝ)*x 1 + (2829840469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047209433/10000000000 : ℝ)^8465 ≤ (12340085324423/100000000000000 : ℝ)^6417 := by
    have hnat : (2047209433 : ℕ)^8465*100000000000000^6417 ≤ 12340085324423^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047209433 10000000000 12340085324423 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036651781/10000000000 : ℝ)^8465 ≤ (20232514271041/50000000000000 : ℝ)^6417 := by
    have hnat : (5036651781 : ℕ)^8465*50000000000000^6417 ≤ 20232514271041^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036651781 10000000000 20232514271041 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829840469/5000000000 : ℝ)^8465 ≤ (23597443059829/50000000000000 : ℝ)^6417 := by
    have hnat : (2829840469 : ℕ)^8465*50000000000000^6417 ≤ 23597443059829^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829840469 5000000000 23597443059829 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047209433/10000000000 : ℝ), (5036651781/10000000000 : ℝ), (2829840469/5000000000 : ℝ)] ![(12340085324423/100000000000000 : ℝ), (20232514271041/50000000000000 : ℝ), (23597443059829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047209433/10000000000 : ℝ)|^8465 ≤ (12340085324423/100000000000000 : ℝ)^6417
        have hw : |(-2047209433/10000000000 : ℝ)|=(2047209433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036651781/10000000000 : ℝ)|^8465 ≤ (20232514271041/50000000000000 : ℝ)^6417
        have hw : |(5036651781/10000000000 : ℝ)|=(5036651781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829840469/5000000000 : ℝ)|^8465 ≤ (23597443059829/50000000000000 : ℝ)^6417
        have hw : |(2829840469/5000000000 : ℝ)|=(2829840469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246969899/10000000000 : ℝ)*x 0 + (-1758307473/10000000000 : ℝ)*x 1 + (2829840757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246969899/10000000000 : ℝ)^8465 ≤ (42708740394003/100000000000000 : ℝ)^6417 := by
    have hnat : (5246969899 : ℕ)^8465*100000000000000^6417 ≤ 42708740394003^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246969899 10000000000 42708740394003 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1758307473/10000000000 : ℝ)^8465 ≤ (2524091783311/25000000000000 : ℝ)^6417 := by
    have hnat : (1758307473 : ℕ)^8465*25000000000000^6417 ≤ 2524091783311^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758307473 10000000000 2524091783311 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829840757/5000000000 : ℝ)^8465 ≤ (9438978491147/20000000000000 : ℝ)^6417 := by
    have hnat : (2829840757 : ℕ)^8465*20000000000000^6417 ≤ 9438978491147^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829840757 5000000000 9438978491147 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246969899/10000000000 : ℝ), (-1758307473/10000000000 : ℝ), (2829840757/5000000000 : ℝ)] ![(42708740394003/100000000000000 : ℝ), (2524091783311/25000000000000 : ℝ), (9438978491147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246969899/10000000000 : ℝ)|^8465 ≤ (42708740394003/100000000000000 : ℝ)^6417
        have hw : |(5246969899/10000000000 : ℝ)|=(5246969899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1758307473/10000000000 : ℝ)|^8465 ≤ (2524091783311/25000000000000 : ℝ)^6417
        have hw : |(-1758307473/10000000000 : ℝ)|=(1758307473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829840757/5000000000 : ℝ)|^8465 ≤ (9438978491147/20000000000000 : ℝ)^6417
        have hw : |(2829840757/5000000000 : ℝ)|=(2829840757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1049393963/2000000000 : ℝ)*x 0 + (5659681173/10000000000 : ℝ)*x 1 + (-219788511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049393963/2000000000 : ℝ)^8465 ≤ (21354369746027/50000000000000 : ℝ)^6417 := by
    have hnat : (1049393963 : ℕ)^8465*50000000000000^6417 ≤ 21354369746027^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049393963 2000000000 21354369746027 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5659681173/10000000000 : ℝ)^8465 ≤ (4719488870469/10000000000000 : ℝ)^6417 := by
    have hnat : (5659681173 : ℕ)^8465*10000000000000^6417 ≤ 4719488870469^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659681173 10000000000 4719488870469 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219788511/1250000000 : ℝ)^8465 ≤ (5048185895841/50000000000000 : ℝ)^6417 := by
    have hnat : (219788511 : ℕ)^8465*50000000000000^6417 ≤ 5048185895841^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219788511 1250000000 5048185895841 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049393963/2000000000 : ℝ), (5659681173/10000000000 : ℝ), (-219788511/1250000000 : ℝ)] ![(21354369746027/50000000000000 : ℝ), (4719488870469/10000000000000 : ℝ), (5048185895841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049393963/2000000000 : ℝ)|^8465 ≤ (21354369746027/50000000000000 : ℝ)^6417
        have hw : |(1049393963/2000000000 : ℝ)|=(1049393963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5659681173/10000000000 : ℝ)|^8465 ≤ (4719488870469/10000000000000 : ℝ)^6417
        have hw : |(5659681173/10000000000 : ℝ)|=(5659681173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219788511/1250000000 : ℝ)|^8465 ≤ (5048185895841/50000000000000 : ℝ)^6417
        have hw : |(-219788511/1250000000 : ℝ)|=(219788511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s1_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (430755163/1000000000 : ℝ)*x 0 + (623660273/1250000000 : ℝ)*x 1 + (1859048917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430755163/1000000000 : ℝ)^8465 ≤ (16461307725833/50000000000000 : ℝ)^6417 := by
    have hnat : (430755163 : ℕ)^8465*50000000000000^6417 ≤ 16461307725833^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430755163 1000000000 16461307725833 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623660273/1250000000 : ℝ)^8465 ≤ (249773439363/625000000000 : ℝ)^6417 := by
    have hnat : (623660273 : ℕ)^8465*625000000000^6417 ≤ 249773439363^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623660273 1250000000 249773439363 625000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859048917/5000000000 : ℝ)^8465 ≤ (27113634235083/100000000000000 : ℝ)^6417 := by
    have hnat : (1859048917 : ℕ)^8465*100000000000000^6417 ≤ 27113634235083^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859048917 5000000000 27113634235083 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430755163/1000000000 : ℝ), (623660273/1250000000 : ℝ), (1859048917/5000000000 : ℝ)] ![(16461307725833/50000000000000 : ℝ), (249773439363/625000000000 : ℝ), (27113634235083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430755163/1000000000 : ℝ)|^8465 ≤ (16461307725833/50000000000000 : ℝ)^6417
        have hw : |(430755163/1000000000 : ℝ)|=(430755163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623660273/1250000000 : ℝ)|^8465 ≤ (249773439363/625000000000 : ℝ)^6417
        have hw : |(623660273/1250000000 : ℝ)|=(623660273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859048917/5000000000 : ℝ)|^8465 ≤ (27113634235083/100000000000000 : ℝ)^6417
        have hw : |(1859048917/5000000000 : ℝ)|=(1859048917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19873/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6831/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6831/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6831/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6831/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6831/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6831/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (937/100000 : ℝ) ^ (529/128 : ℝ) ≤ (207276483587/50000000000000000000 : ℝ) := by
    have hpowers : (937/100000 : ℝ)^529 ≤ (207276483587/50000000000000000000 : ℝ)^128 := by
      have hnat : (937 : ℕ)^529*50000000000000000000^128 ≤ 207276483587^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        937 100000 207276483587 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (937/100000 : ℝ)) (X := (207276483587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (6831/25000 : ℝ) ^ (529/128 : ℝ) ≤ (93836789176193537/20000000000000000000 : ℝ) := by
    have hpowers : (6831/25000 : ℝ)^529 ≤ (93836789176193537/20000000000000000000 : ℝ)^128 := by
      have hnat : (6831 : ℕ)^529*20000000000000000000^128 ≤ 93836789176193537^128*25000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6831 25000 93836789176193537 20000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6831/25000 : ℝ)) (X := (93836789176193537/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000207276483587/25000000000000000000 : ℝ) ≤ (10000000020061543/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25000000207276483587/25000000000000000000 : ℝ)^128 ≤ (10000000020061543/10000000000000000 : ℝ)^529 := by
      have hnat : (25000000207276483587 : ℕ)^128*10000000000000000^529 ≤ 10000000020061543^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000207276483587 25000000000000000000 10000000020061543 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000020061543/10000000000000000 : ℝ)) (X := (25000000207276483587/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100469184360433934859/100000000000000000000 : ℝ) ≤ (2002266506413601/2000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (100469184360433934859/100000000000000000000 : ℝ)^128 ≤ (2002266506413601/2000000000000000 : ℝ)^529 := by
      have hnat : (100469184360433934859 : ℕ)^128*2000000000000000^529 ≤ 2002266506413601^529*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100469184360433934859 100000000000000000000 2002266506413601 2000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002266506413601/2000000000000000 : ℝ)) (X := (100469184360433934859/100000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10093836789176193537/10000000000000000000 : ℝ) ≤ (10022665044074467/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (10093836789176193537/10000000000000000000 : ℝ)^128 ≤ (10022665044074467/10000000000000000 : ℝ)^529 := by
      have hnat : (10093836789176193537 : ℕ)^128*10000000000000000^529 ≤ 10022665044074467^529*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10093836789176193537 10000000000000000000 10022665044074467 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022665044074467/10000000000000000 : ℝ)) (X := (10093836789176193537/10000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(207276483587/50000000000000000000 : ℝ) ≤ ((263848763401863825353/263870000000000000000 : ℝ)+2*(5666256003231/1319350000000000 : ℝ)*(937/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (263848763401863825353/263870000000000000000 : ℝ)+2*(5666256003231/1319350000000000 : ℝ)*(937/100000 : ℝ)=(10000000020061543/10000000000000000 : ℝ) by norm_num, show 1+2*(207276483587/50000000000000000000 : ℝ)=(25000000207276483587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93836789176193537/20000000000000000000 : ℝ)+(207276483587/50000000000000000000 : ℝ) ≤ ((263848763401863825353/263870000000000000000 : ℝ)+(5666256003231/1319350000000000 : ℝ)*((6831/25000 : ℝ)+(937/100000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (263848763401863825353/263870000000000000000 : ℝ)+(5666256003231/1319350000000000 : ℝ)*((6831/25000 : ℝ)+(937/100000 : ℝ))=(2002266506413601/2000000000000000 : ℝ) by norm_num, show 1+(93836789176193537/20000000000000000000 : ℝ)+(207276483587/50000000000000000000 : ℝ)=(100469184360433934859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93836789176193537/20000000000000000000 : ℝ) ≤ ((263848763401863825353/263870000000000000000 : ℝ)+2*(5666256003231/1319350000000000 : ℝ)*(6831/25000 : ℝ))^(529/128 : ℝ) := by
    rw [show (263848763401863825353/263870000000000000000 : ℝ)+2*(5666256003231/1319350000000000 : ℝ)*(6831/25000 : ℝ)=(10022665044074467/10000000000000000 : ℝ) by norm_num, show 1+2*(93836789176193537/20000000000000000000 : ℝ)=(10093836789176193537/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (263848763401863825353/263870000000000000000 : ℝ)*(X 1 0+X 2 0)+(5666256003231/1319350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (937/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (263848763401863825353/263870000000000000000 : ℝ)) (alpha := (5666256003231/1319350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (263848763401863825353/263870000000000000000 : ℝ)*(X 0 1+X 2 1)+(5666256003231/1319350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (937/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (263848763401863825353/263870000000000000000 : ℝ)) (alpha := (5666256003231/1319350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (263848763401863825353/263870000000000000000 : ℝ)*(X 0 2+X 1 2)+(5666256003231/1319350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (937/100000 : ℝ)) (hi := (6831/25000 : ℝ)) (c := (263848763401863825353/263870000000000000000 : ℝ)) (alpha := (5666256003231/1319350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2046567799/10000000000 : ℝ)*X 0 0+(5668142889/10000000000 : ℝ)*X 0 1+(5028346023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706015629/5000000000 : ℝ)*X 1 0+(-477928529/2000000000 : ℝ)*X 1 1+(628543271/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412031383/10000000000 : ℝ)*X 2 0+(314271631/625000000 : ℝ)*X 2 1+(-2389642573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153121497/5000000000 : ℝ)*X 0 0+(740166541/2000000000 : ℝ)*X 0 1+(1001245677/2000000000 : ℝ)*X 0 2+(2153121497/5000000000 : ℝ)*X 1 0+(740166541/2000000000 : ℝ)*X 1 1+(1001245677/2000000000 : ℝ)*X 1 2+(2153121497/5000000000 : ℝ)*X 2 0+(740166541/2000000000 : ℝ)*X 2 1+(1001245677/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047209433/10000000000 : ℝ)*X 0 0+(5036651781/10000000000 : ℝ)*X 0 1+(2829840469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246969899/10000000000 : ℝ)*X 1 0+(-1758307473/10000000000 : ℝ)*X 1 1+(2829840757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049393963/2000000000 : ℝ)*X 2 0+(5659681173/10000000000 : ℝ)*X 2 1+(-219788511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430755163/1000000000 : ℝ)*X 0 0+(623660273/1250000000 : ℝ)*X 0 1+(1859048917/5000000000 : ℝ)*X 0 2+(430755163/1000000000 : ℝ)*X 1 0+(623660273/1250000000 : ℝ)*X 1 1+(1859048917/5000000000 : ℝ)*X 1 2+(430755163/1000000000 : ℝ)*X 2 0+(623660273/1250000000 : ℝ)*X 2 1+(1859048917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2282512471382492774529886239/824593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17546083/100000000000000 : ℝ)*(base1) + (159941789/25000000000000 : ℝ)*(base19) + (675867357/100000000000000 : ℝ)*(base23) + (63043171/100000000000000 : ℝ)*(upper3) + (99608789/100000000000000 : ℝ)*(upper5) + (72783109339771/6250000000000 : ℝ)*(major0) + (72783109339771/6250000000000 : ℝ)*(major1) + (72783109339771/6250000000000 : ℝ)*(major2) + (781499885145057/50000000000000 : ℝ)*(sp0) + (1563003371694177/100000000000000 : ℝ)*(sp1) + (195375416949247/12500000000000 : ℝ)*(sp2) + (30642134163993/4000000000000 : ℝ)*(sp3) + (2129358651/50000000000000 : ℝ)*(sp4) + (505874317/25000000000000 : ℝ)*(sp7) + (30642215805727/4000000000000 : ℝ)*(f.failure) + (1563004011461333/100000000000000 : ℝ)*(f.sum) + (47746587300149/65967500000000000000000000000 : ℝ)*base66 + (2805172615419026663/1649187500000000000000000000000000 : ℝ)*base67 + (3114737459670348337/1649187500000000000000000000000000 : ℝ)*base70 + (1495979977459535837/1649187500000000000000000000000000 : ℝ)*base72 + (133762719091103/32983750000000000000000000000 : ℝ)*base73 + (6145214876626973337/1649187500000000000000000000000000 : ℝ)*base76 + (2678718115894160837/1649187500000000000000000000000000 : ℝ)*base78 + (2754371888053026663/1649187500000000000000000000000000 : ℝ)*base79 + (210512134398017/131935000000000000000000000000 : ℝ)*base81 + (59803/400000000000000000000 : ℝ)*base89 + (59803/400000000000000000000 : ℝ)*base91 + (59803/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1035715210141452999746212671/131935000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4482231/50000000000000 : ℝ)*(base1) + (299221099/20000000000000 : ℝ)*(base19) + (357948479/25000000000000 : ℝ)*(base23) + (220346909/100000000000000 : ℝ)*(upper3) + (168517009/100000000000000 : ℝ)*(upper5) + (23917289429469/2000000000000 : ℝ)*(major0) + (23917289429469/2000000000000 : ℝ)*(major1) + (23917289429469/2000000000000 : ℝ)*(major2) + (817930467/10000000000000 : ℝ)*(sp1) + (6951776861/100000000000000 : ℝ)*(sp2) + (802530284449707/50000000000000 : ℝ)*(sp4) + (1605050884524787/100000000000000 : ℝ)*(sp5) + (100315761022761/6250000000000 : ℝ)*(sp6) + (786668112374383/100000000000000 : ℝ)*(sp7) + (157333624267769/20000000000000 : ℝ)*(f.failure) + (200632569991869/12500000000000 : ℝ)*(f.sum) + (2117459841743/3298375000000000000000000000 : ℝ)*base65 + (157307438783112443/527740000000000000000000000000000 : ℝ)*base68 + (2306110591260632443/527740000000000000000000000000000 : ℝ)*base70 + (207129713496292443/527740000000000000000000000000000 : ℝ)*base72 + (10831482904303/26387000000000000000000000000 : ℝ)*base73 + (2494992582505327557/527740000000000000000000000000000 : ℝ)*base75 + (1373865131880492443/527740000000000000000000000000000 : ℝ)*base78 + (2816265672782912443/527740000000000000000000000000000 : ℝ)*base80 + (88616383893067/26387000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12466141/2000000000000000000000 : ℝ)*base89 + (12466141/2000000000000000000000 : ℝ)*base91 + (12466141/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1271_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6831/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19873/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s2_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093125283/10000000000 : ℝ)*x 0 + (685970293/1250000000 : ℝ)*x 1 + (5179009041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093125283/10000000000 : ℝ)^8465 ≤ (12706486803687/100000000000000 : ℝ)^6417 := by
    have hnat : (2093125283 : ℕ)^8465*100000000000000^6417 ≤ 12706486803687^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093125283 10000000000 12706486803687 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685970293/1250000000 : ℝ)^8465 ≤ (45312989657363/100000000000000 : ℝ)^6417 := by
    have hnat : (685970293 : ℕ)^8465*100000000000000^6417 ≤ 45312989657363^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685970293 1250000000 45312989657363 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179009041/10000000000 : ℝ)^8465 ≤ (8396104703887/20000000000000 : ℝ)^6417 := by
    have hnat : (5179009041 : ℕ)^8465*20000000000000^6417 ≤ 8396104703887^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179009041 10000000000 8396104703887 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093125283/10000000000 : ℝ), (685970293/1250000000 : ℝ), (5179009041/10000000000 : ℝ)] ![(12706486803687/100000000000000 : ℝ), (45312989657363/100000000000000 : ℝ), (8396104703887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093125283/10000000000 : ℝ)|^8465 ≤ (12706486803687/100000000000000 : ℝ)^6417
        have hw : |(-2093125283/10000000000 : ℝ)|=(2093125283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685970293/1250000000 : ℝ)|^8465 ≤ (45312989657363/100000000000000 : ℝ)^6417
        have hw : |(685970293/1250000000 : ℝ)|=(685970293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179009041/10000000000 : ℝ)|^8465 ≤ (8396104703887/20000000000000 : ℝ)^6417
        have hw : |(5179009041/10000000000 : ℝ)|=(5179009041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368478939/10000000000 : ℝ)*x 0 + (-563223289/2500000000 : ℝ)*x 1 + (207160373/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368478939/10000000000 : ℝ)^8465 ≤ (2751139993489/6250000000000 : ℝ)^6417 := by
    have hnat : (5368478939 : ℕ)^8465*6250000000000^6417 ≤ 2751139993489^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368478939 10000000000 2751139993489 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563223289/2500000000 : ℝ)^8465 ≤ (14001233527389/100000000000000 : ℝ)^6417 := by
    have hnat : (563223289 : ℕ)^8465*100000000000000^6417 ≤ 14001233527389^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563223289 2500000000 14001233527389 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207160373/400000000 : ℝ)^8465 ≤ (41980526556223/100000000000000 : ℝ)^6417 := by
    have hnat : (207160373 : ℕ)^8465*100000000000000^6417 ≤ 41980526556223^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207160373 400000000 41980526556223 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368478939/10000000000 : ℝ), (-563223289/2500000000 : ℝ), (207160373/400000000 : ℝ)] ![(2751139993489/6250000000000 : ℝ), (14001233527389/100000000000000 : ℝ), (41980526556223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368478939/10000000000 : ℝ)|^8465 ≤ (2751139993489/6250000000000 : ℝ)^6417
        have hw : |(5368478939/10000000000 : ℝ)|=(5368478939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563223289/2500000000 : ℝ)|^8465 ≤ (14001233527389/100000000000000 : ℝ)^6417
        have hw : |(-563223289/2500000000 : ℝ)|=(563223289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207160373/400000000 : ℝ)|^8465 ≤ (41980526556223/100000000000000 : ℝ)^6417
        have hw : |(207160373/400000000 : ℝ)|=(207160373/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684239453/5000000000 : ℝ)*x 0 + (5179009299/10000000000 : ℝ)*x 1 + (-450578647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684239453/5000000000 : ℝ)^8465 ≤ (5502279942361/12500000000000 : ℝ)^6417 := by
    have hnat : (2684239453 : ℕ)^8465*12500000000000^6417 ≤ 5502279942361^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684239453 5000000000 5502279942361 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179009299/10000000000 : ℝ)^8465 ≤ (41980526278207/100000000000000 : ℝ)^6417 := by
    have hnat : (5179009299 : ℕ)^8465*100000000000000^6417 ≤ 41980526278207^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179009299 10000000000 41980526278207 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450578647/2000000000 : ℝ)^8465 ≤ (280024683501/2000000000000 : ℝ)^6417 := by
    have hnat : (450578647 : ℕ)^8465*2000000000000^6417 ≤ 280024683501^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450578647 2000000000 280024683501 2000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684239453/5000000000 : ℝ), (5179009299/10000000000 : ℝ), (-450578647/2000000000 : ℝ)] ![(5502279942361/12500000000000 : ℝ), (41980526278207/100000000000000 : ℝ), (280024683501/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684239453/5000000000 : ℝ)|^8465 ≤ (5502279942361/12500000000000 : ℝ)^6417
        have hw : |(2684239453/5000000000 : ℝ)|=(2684239453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179009299/10000000000 : ℝ)|^8465 ≤ (41980526278207/100000000000000 : ℝ)^6417
        have hw : |(5179009299/10000000000 : ℝ)|=(5179009299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450578647/2000000000 : ℝ)|^8465 ≤ (280024683501/2000000000000 : ℝ)^6417
        have hw : |(-450578647/2000000000 : ℝ)|=(450578647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (867692829/2000000000 : ℝ)*x 0 + (504310759/1250000000 : ℝ)*x 1 + (466444321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867692829/2000000000 : ℝ)^8465 ≤ (664692808473/2000000000000 : ℝ)^6417 := by
    have hnat : (867692829 : ℕ)^8465*2000000000000^6417 ≤ 664692808473^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867692829 2000000000 664692808473 2000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504310759/1250000000 : ℝ)^8465 ≤ (30197754034511/100000000000000 : ℝ)^6417 := by
    have hnat : (504310759 : ℕ)^8465*100000000000000^6417 ≤ 30197754034511^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504310759 1250000000 30197754034511 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466444321/1000000000 : ℝ)^8465 ≤ (1828380276473/5000000000000 : ℝ)^6417 := by
    have hnat : (466444321 : ℕ)^8465*5000000000000^6417 ≤ 1828380276473^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466444321 1000000000 1828380276473 5000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867692829/2000000000 : ℝ), (504310759/1250000000 : ℝ), (466444321/1000000000 : ℝ)] ![(664692808473/2000000000000 : ℝ), (30197754034511/100000000000000 : ℝ), (1828380276473/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867692829/2000000000 : ℝ)|^8465 ≤ (664692808473/2000000000000 : ℝ)^6417
        have hw : |(867692829/2000000000 : ℝ)|=(867692829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504310759/1250000000 : ℝ)|^8465 ≤ (30197754034511/100000000000000 : ℝ)^6417
        have hw : |(504310759/1250000000 : ℝ)|=(504310759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466444321/1000000000 : ℝ)|^8465 ≤ (1828380276473/5000000000000 : ℝ)^6417
        have hw : |(466444321/1000000000 : ℝ)|=(466444321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-83727907/400000000 : ℝ)*x 0 + (20723813/40000000 : ℝ)*x 1 + (171431259/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83727907/400000000 : ℝ)^8465 ≤ (3176766630881/25000000000000 : ℝ)^6417 := by
    have hnat : (83727907 : ℕ)^8465*25000000000000^6417 ≤ 3176766630881^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83727907 400000000 3176766630881 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20723813/40000000 : ℝ)^8465 ≤ (21000657012897/50000000000000 : ℝ)^6417 := by
    have hnat : (20723813 : ℕ)^8465*50000000000000^6417 ≤ 21000657012897^6417*40000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20723813 40000000 21000657012897 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171431259/312500000 : ℝ)^8465 ≤ (2830726214929/6250000000000 : ℝ)^6417 := by
    have hnat : (171431259 : ℕ)^8465*6250000000000^6417 ≤ 2830726214929^6417*312500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171431259 312500000 2830726214929 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83727907/400000000 : ℝ), (20723813/40000000 : ℝ), (171431259/312500000 : ℝ)] ![(3176766630881/25000000000000 : ℝ), (21000657012897/50000000000000 : ℝ), (2830726214929/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83727907/400000000 : ℝ)|^8465 ≤ (3176766630881/25000000000000 : ℝ)^6417
        have hw : |(-83727907/400000000 : ℝ)|=(83727907/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20723813/40000000 : ℝ)|^8465 ≤ (21000657012897/50000000000000 : ℝ)^6417
        have hw : |(20723813/40000000 : ℝ)|=(20723813/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171431259/312500000 : ℝ)|^8465 ≤ (2830726214929/6250000000000 : ℝ)^6417
        have hw : |(171431259/312500000 : ℝ)|=(171431259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644742987/5000000000 : ℝ)*x 0 + (-1946101901/10000000000 : ℝ)*x 1 + (5485800329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644742987/5000000000 : ℝ)^8465 ≤ (43165845895371/100000000000000 : ℝ)^6417 := by
    have hnat : (2644742987 : ℕ)^8465*100000000000000^6417 ≤ 43165845895371^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644742987 5000000000 43165845895371 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946101901/10000000000 : ℝ)^8465 ≤ (2308506840223/20000000000000 : ℝ)^6417 := by
    have hnat : (1946101901 : ℕ)^8465*20000000000000^6417 ≤ 2308506840223^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946101901 10000000000 2308506840223 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485800329/10000000000 : ℝ)^8465 ≤ (45291619885401/100000000000000 : ℝ)^6417 := by
    have hnat : (5485800329 : ℕ)^8465*100000000000000^6417 ≤ 45291619885401^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485800329 10000000000 45291619885401 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644742987/5000000000 : ℝ), (-1946101901/10000000000 : ℝ), (5485800329/10000000000 : ℝ)] ![(43165845895371/100000000000000 : ℝ), (2308506840223/20000000000000 : ℝ), (45291619885401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644742987/5000000000 : ℝ)|^8465 ≤ (43165845895371/100000000000000 : ℝ)^6417
        have hw : |(2644742987/5000000000 : ℝ)|=(2644742987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946101901/10000000000 : ℝ)|^8465 ≤ (2308506840223/20000000000000 : ℝ)^6417
        have hw : |(-1946101901/10000000000 : ℝ)|=(1946101901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485800329/10000000000 : ℝ)|^8465 ≤ (45291619885401/100000000000000 : ℝ)^6417
        have hw : |(5485800329/10000000000 : ℝ)|=(5485800329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289486073/10000000000 : ℝ)*x 0 + (5485800453/10000000000 : ℝ)*x 1 + (-973050797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289486073/10000000000 : ℝ)^8465 ≤ (345326775689/800000000000 : ℝ)^6417 := by
    have hnat : (5289486073 : ℕ)^8465*800000000000^6417 ≤ 345326775689^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289486073 10000000000 345326775689 800000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485800453/10000000000 : ℝ)^8465 ≤ (452916212359/1000000000000 : ℝ)^6417 := by
    have hnat : (5485800453 : ℕ)^8465*1000000000000^6417 ≤ 452916212359^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485800453 10000000000 452916212359 1000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973050797/5000000000 : ℝ)^8465 ≤ (11542531799137/100000000000000 : ℝ)^6417 := by
    have hnat : (973050797 : ℕ)^8465*100000000000000^6417 ≤ 11542531799137^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973050797 5000000000 11542531799137 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289486073/10000000000 : ℝ), (5485800453/10000000000 : ℝ), (-973050797/5000000000 : ℝ)] ![(345326775689/800000000000 : ℝ), (452916212359/1000000000000 : ℝ), (11542531799137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289486073/10000000000 : ℝ)|^8465 ≤ (345326775689/800000000000 : ℝ)^6417
        have hw : |(5289486073/10000000000 : ℝ)|=(5289486073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485800453/10000000000 : ℝ)|^8465 ≤ (452916212359/1000000000000 : ℝ)^6417
        have hw : |(5485800453/10000000000 : ℝ)|=(5485800453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973050797/5000000000 : ℝ)|^8465 ≤ (11542531799137/100000000000000 : ℝ)^6417
        have hw : |(-973050797/5000000000 : ℝ)|=(973050797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s2_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2169305739/5000000000 : ℝ)*x 0 + (4660476979/10000000000 : ℝ)*x 1 + (4038488293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169305739/5000000000 : ℝ)^8465 ≤ (33236129278227/100000000000000 : ℝ)^6417 := by
    have hnat : (2169305739 : ℕ)^8465*100000000000000^6417 ≤ 33236129278227^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169305739 5000000000 33236129278227 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4660476979/10000000000 : ℝ)^8465 ≤ (36526593553251/100000000000000 : ℝ)^6417 := by
    have hnat : (4660476979 : ℕ)^8465*100000000000000^6417 ≤ 36526593553251^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660476979 10000000000 36526593553251 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038488293/10000000000 : ℝ)^8465 ≤ (30237277147173/100000000000000 : ℝ)^6417 := by
    have hnat : (4038488293 : ℕ)^8465*100000000000000^6417 ≤ 30237277147173^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038488293 10000000000 30237277147173 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169305739/5000000000 : ℝ), (4660476979/10000000000 : ℝ), (4038488293/10000000000 : ℝ)] ![(33236129278227/100000000000000 : ℝ), (36526593553251/100000000000000 : ℝ), (30237277147173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169305739/5000000000 : ℝ)|^8465 ≤ (33236129278227/100000000000000 : ℝ)^6417
        have hw : |(2169305739/5000000000 : ℝ)|=(2169305739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4660476979/10000000000 : ℝ)|^8465 ≤ (36526593553251/100000000000000 : ℝ)^6417
        have hw : |(4660476979/10000000000 : ℝ)|=(4660476979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038488293/10000000000 : ℝ)|^8465 ≤ (30237277147173/100000000000000 : ℝ)^6417
        have hw : |(4038488293/10000000000 : ℝ)|=(4038488293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9619/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8073/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6347/100000 : ℝ) ^ (529/128 : ℝ) ≤ (70326683833041/6250000000000000000 : ℝ) := by
    have hpowers : (6347/100000 : ℝ)^529 ≤ (70326683833041/6250000000000000000 : ℝ)^128 := by
      have hnat : (6347 : ℕ)^529*6250000000000000000^128 ≤ 70326683833041^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6347 100000 70326683833041 6250000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6347/100000 : ℝ)) (X := (70326683833041/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (19873/100000 : ℝ) ^ (529/128 : ℝ) ≤ (6292516262642717/5000000000000000000 : ℝ) := by
    have hpowers : (19873/100000 : ℝ)^529 ≤ (6292516262642717/5000000000000000000 : ℝ)^128 := by
      have hnat : (19873 : ℕ)^529*5000000000000000000^128 ≤ 6292516262642717^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19873 100000 6292516262642717 5000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19873/100000 : ℝ)) (X := (6292516262642717/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125070326683833041/3125000000000000000 : ℝ) ≤ (10000054452862003/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (3125070326683833041/3125000000000000000 : ℝ)^128 ≤ (10000054452862003/10000000000000000 : ℝ)^529 := by
      have hnat : (3125070326683833041 : ℕ)^128*10000000000000000^529 ≤ 10000054452862003^529*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125070326683833041 3125000000000000000 10000054452862003 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054452862003/10000000000000000 : ℝ)) (X := (3125070326683833041/3125000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25031743888048545749/25000000000000000000 : ℝ) ≤ (2000614179760171/2000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25031743888048545749/25000000000000000000 : ℝ)^128 ≤ (2000614179760171/2000000000000000 : ℝ)^529 := by
      have hnat : (25031743888048545749 : ℕ)^128*2000000000000000^529 ≤ 2000614179760171^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031743888048545749 25000000000000000000 2000614179760171 2000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000614179760171/2000000000000000 : ℝ)) (X := (25031743888048545749/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2506292516262642717/2500000000000000000 : ℝ) ≤ (10006087344739707/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (2506292516262642717/2500000000000000000 : ℝ)^128 ≤ (10006087344739707/10000000000000000 : ℝ)^529 := by
      have hnat : (2506292516262642717 : ℕ)^128*10000000000000000^529 ≤ 10006087344739707^529*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2506292516262642717 2500000000000000000 10006087344739707 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006087344739707/10000000000000000 : ℝ)) (X := (2506292516262642717/2500000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70326683833041/6250000000000000000 : ℝ) ≤ ((13522244576466366529/13526000000000000000 : ℝ)+2*(754111484713/338150000000000 : ℝ)*(6347/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (13522244576466366529/13526000000000000000 : ℝ)+2*(754111484713/338150000000000 : ℝ)*(6347/100000 : ℝ)=(10000054452862003/10000000000000000 : ℝ) by norm_num, show 1+2*(70326683833041/6250000000000000000 : ℝ)=(3125070326683833041/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6292516262642717/5000000000000000000 : ℝ)+(70326683833041/6250000000000000000 : ℝ) ≤ ((13522244576466366529/13526000000000000000 : ℝ)+(754111484713/338150000000000 : ℝ)*((19873/100000 : ℝ)+(6347/100000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (13522244576466366529/13526000000000000000 : ℝ)+(754111484713/338150000000000 : ℝ)*((19873/100000 : ℝ)+(6347/100000 : ℝ))=(2000614179760171/2000000000000000 : ℝ) by norm_num, show 1+(6292516262642717/5000000000000000000 : ℝ)+(70326683833041/6250000000000000000 : ℝ)=(25031743888048545749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6292516262642717/5000000000000000000 : ℝ) ≤ ((13522244576466366529/13526000000000000000 : ℝ)+2*(754111484713/338150000000000 : ℝ)*(19873/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (13522244576466366529/13526000000000000000 : ℝ)+2*(754111484713/338150000000000 : ℝ)*(19873/100000 : ℝ)=(10006087344739707/10000000000000000 : ℝ) by norm_num, show 1+2*(6292516262642717/5000000000000000000 : ℝ)=(2506292516262642717/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13522244576466366529/13526000000000000000 : ℝ)*(X 1 0+X 2 0)+(754111484713/338150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (6347/100000 : ℝ)) (hi := (19873/100000 : ℝ)) (c := (13522244576466366529/13526000000000000000 : ℝ)) (alpha := (754111484713/338150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13522244576466366529/13526000000000000000 : ℝ)*(X 0 1+X 2 1)+(754111484713/338150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (6347/100000 : ℝ)) (hi := (19873/100000 : ℝ)) (c := (13522244576466366529/13526000000000000000 : ℝ)) (alpha := (754111484713/338150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13522244576466366529/13526000000000000000 : ℝ)*(X 0 2+X 1 2)+(754111484713/338150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (6347/100000 : ℝ)) (hi := (19873/100000 : ℝ)) (c := (13522244576466366529/13526000000000000000 : ℝ)) (alpha := (754111484713/338150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2093125283/10000000000 : ℝ)*X 0 0+(685970293/1250000000 : ℝ)*X 0 1+(5179009041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368478939/10000000000 : ℝ)*X 1 0+(-563223289/2500000000 : ℝ)*X 1 1+(207160373/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684239453/5000000000 : ℝ)*X 2 0+(5179009299/10000000000 : ℝ)*X 2 1+(-450578647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867692829/2000000000 : ℝ)*X 0 0+(504310759/1250000000 : ℝ)*X 0 1+(466444321/1000000000 : ℝ)*X 0 2+(867692829/2000000000 : ℝ)*X 1 0+(504310759/1250000000 : ℝ)*X 1 1+(466444321/1000000000 : ℝ)*X 1 2+(867692829/2000000000 : ℝ)*X 2 0+(504310759/1250000000 : ℝ)*X 2 1+(466444321/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-83727907/400000000 : ℝ)*X 0 0+(20723813/40000000 : ℝ)*X 0 1+(171431259/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644742987/5000000000 : ℝ)*X 1 0+(-1946101901/10000000000 : ℝ)*X 1 1+(5485800329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289486073/10000000000 : ℝ)*X 2 0+(5485800453/10000000000 : ℝ)*X 2 1+(-973050797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169305739/5000000000 : ℝ)*X 0 0+(4660476979/10000000000 : ℝ)*X 0 1+(4038488293/10000000000 : ℝ)*X 0 2+(2169305739/5000000000 : ℝ)*X 1 0+(4660476979/10000000000 : ℝ)*X 1 1+(4038488293/10000000000 : ℝ)*X 1 2+(2169305739/5000000000 : ℝ)*X 2 0+(4660476979/10000000000 : ℝ)*X 2 1+(4038488293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (751018344470067225783419103/84537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1611854869/100000000000000 : ℝ)*(base19) + (1521351429/100000000000000 : ℝ)*(base23) + (378983/1000000000000 : ℝ)*(lower2) + (241525247/100000000000000 : ℝ)*(upper3) + (24436979/20000000000000 : ℝ)*(upper5) + (301643973324123/12500000000000 : ℝ)*(major0) + (301643973324123/12500000000000 : ℝ)*(major1) + (301643973324123/12500000000000 : ℝ)*(major2) + (1619427061535839/50000000000000 : ℝ)*(sp0) + (1619436482962107/50000000000000 : ℝ)*(sp1) + (1619436528213827/50000000000000 : ℝ)*(sp2) + (1587418496109793/100000000000000 : ℝ)*(sp3) + (5113676851/25000000000000 : ℝ)*(sp4) + (10203168799/100000000000000 : ℝ)*(sp7) + (6200893356557/390625000000 : ℝ)*(f.failure) + (1619437288889541/50000000000000 : ℝ)*(f.sum) + (63559916343211/33815000000000000000000000000 : ℝ)*base66 + (586149282993735933/169075000000000000000000000000000 : ℝ)*base68 + (874128176808585933/169075000000000000000000000000000 : ℝ)*base70 + (1732974576742535933/169075000000000000000000000000000 : ℝ)*base72 + (99733543742789/33815000000000000000000000000 : ℝ)*base73 + (3693846461588585933/169075000000000000000000000000000 : ℝ)*base76 + (1848780397742885933/169075000000000000000000000000000 : ℝ)*base78 + (2799780342933285933/169075000000000000000000000000000 : ℝ)*base80 + (954102175621/33815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (237673/39062500000000000000 : ℝ)*base89 + (237673/39062500000000000000 : ℝ)*base91 + (237673/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2257147599716538199320675291/676300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (264964869/25000000000000 : ℝ)*(base19) + (20773007/1562500000000 : ℝ)*(base23) + (12132237/20000000000000 : ℝ)*(upper2) + (40143297/25000000000000 : ℝ)*(upper3) + (59737057/100000000000000 : ℝ)*(upper5) + (2444039360514807/100000000000000 : ℝ)*(major0) + (2444039360514807/100000000000000 : ℝ)*(major1) + (2444039360514807/100000000000000 : ℝ)*(major2) + (431978639/4000000000000 : ℝ)*(sp1) + (8531352113/50000000000000 : ℝ)*(sp2) + (102510354030681/3125000000000 : ℝ)*(sp4) + (3280319469656341/100000000000000 : ℝ)*(sp5) + (3280312936805119/100000000000000 : ℝ)*(sp6) + (803873640398999/50000000000000 : ℝ)*(sp7) + (803873640398999/50000000000000 : ℝ)*(f.failure) + (102510354030681/3125000000000 : ℝ)*(f.sum) + (36540624185961/16907500000000000000000000000 : ℝ)*base65 + (4669716480000134903/1352600000000000000000000000000000 : ℝ)*base67 + (7674762353616665097/1352600000000000000000000000000000 : ℝ)*base70 + (263120623931534903/1352600000000000000000000000000000 : ℝ)*base71 + (9893550046467/33815000000000000000000000000 : ℝ)*base73 + (1496410787466534903/1352600000000000000000000000000000 : ℝ)*base75 + (1467742418293134903/1352600000000000000000000000000000 : ℝ)*base77 + (9221881129800465097/1352600000000000000000000000000000 : ℝ)*base80 + (23478478049611/4226875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2805389/5000000000000000000000 : ℝ)*base90 + (2805389/5000000000000000000000 : ℝ)*base92 + (2805389/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1271_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1271_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1271_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1271_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1271_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
