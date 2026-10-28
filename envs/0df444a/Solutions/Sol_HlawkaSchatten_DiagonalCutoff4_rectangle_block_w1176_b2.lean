-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:47:43.356237+00:00
-- url     : https://prove2.me/submissions/5aa5dd0c-8cbb-4aa3-9c2a-a9219cbc1cf9

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
theorem support_rectangle_w1176_s6_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150706583/10000000000 : ℝ)*x 0 + (5392703643/10000000000 : ℝ)*x 1 + (526600161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150706583/10000000000 : ℝ)^8369 ≤ (522874997329/4000000000000 : ℝ)^6321 := by
    have hnat : (2150706583 : ℕ)^8369*4000000000000^6321 ≤ 522874997329^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150706583 10000000000 522874997329 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392703643/10000000000 : ℝ)^8369 ≤ (44148103038611/100000000000000 : ℝ)^6321 := by
    have hnat : (5392703643 : ℕ)^8369*100000000000000^6321 ≤ 44148103038611^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392703643 10000000000 44148103038611 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526600161/1000000000 : ℝ)^8369 ≤ (42780022018673/100000000000000 : ℝ)^6321 := by
    have hnat : (526600161 : ℕ)^8369*100000000000000^6321 ≤ 42780022018673^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526600161 1000000000 42780022018673 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150706583/10000000000 : ℝ), (5392703643/10000000000 : ℝ), (526600161/1000000000 : ℝ)] ![(522874997329/4000000000000 : ℝ), (44148103038611/100000000000000 : ℝ), (42780022018673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150706583/10000000000 : ℝ)|^8369 ≤ (522874997329/4000000000000 : ℝ)^6321
        have hw : |(-2150706583/10000000000 : ℝ)|=(2150706583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392703643/10000000000 : ℝ)|^8369 ≤ (44148103038611/100000000000000 : ℝ)^6321
        have hw : |(5392703643/10000000000 : ℝ)|=(5392703643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526600161/1000000000 : ℝ)|^8369 ≤ (42780022018673/100000000000000 : ℝ)^6321
        have hw : |(526600161/1000000000 : ℝ)|=(526600161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668086979/1250000000 : ℝ)*x 0 + (-442993461/2000000000 : ℝ)*x 1 + (5266002039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668086979/1250000000 : ℝ)^8369 ≤ (21814246741643/50000000000000 : ℝ)^6321 := by
    have hnat : (668086979 : ℕ)^8369*50000000000000^6321 ≤ 21814246741643^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668086979 1250000000 21814246741643 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442993461/2000000000 : ℝ)^8369 ≤ (13591479861107/100000000000000 : ℝ)^6321 := by
    have hnat : (442993461 : ℕ)^8369*100000000000000^6321 ≤ 13591479861107^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442993461 2000000000 13591479861107 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266002039/10000000000 : ℝ)^8369 ≤ (8556005326593/20000000000000 : ℝ)^6321 := by
    have hnat : (5266002039 : ℕ)^8369*20000000000000^6321 ≤ 8556005326593^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266002039 10000000000 8556005326593 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668086979/1250000000 : ℝ), (-442993461/2000000000 : ℝ), (5266002039/10000000000 : ℝ)] ![(21814246741643/50000000000000 : ℝ), (13591479861107/100000000000000 : ℝ), (8556005326593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668086979/1250000000 : ℝ)|^8369 ≤ (21814246741643/50000000000000 : ℝ)^6321
        have hw : |(668086979/1250000000 : ℝ)|=(668086979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442993461/2000000000 : ℝ)|^8369 ≤ (13591479861107/100000000000000 : ℝ)^6321
        have hw : |(-442993461/2000000000 : ℝ)|=(442993461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266002039/10000000000 : ℝ)|^8369 ≤ (8556005326593/20000000000000 : ℝ)^6321
        have hw : |(5266002039/10000000000 : ℝ)|=(5266002039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344695841/10000000000 : ℝ)*x 0 + (5266001213/10000000000 : ℝ)*x 1 + (-553742097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344695841/10000000000 : ℝ)^8369 ≤ (10907123395139/25000000000000 : ℝ)^6321 := by
    have hnat : (5344695841 : ℕ)^8369*25000000000000^6321 ≤ 10907123395139^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344695841 10000000000 10907123395139 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266001213/10000000000 : ℝ)^8369 ≤ (42780017748571/100000000000000 : ℝ)^6321 := by
    have hnat : (5266001213 : ℕ)^8369*100000000000000^6321 ≤ 42780017748571^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266001213 10000000000 42780017748571 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553742097/2500000000 : ℝ)^8369 ≤ (54365954639/400000000000 : ℝ)^6321 := by
    have hnat : (553742097 : ℕ)^8369*400000000000^6321 ≤ 54365954639^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553742097 2500000000 54365954639 400000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344695841/10000000000 : ℝ), (5266001213/10000000000 : ℝ), (-553742097/2500000000 : ℝ)] ![(10907123395139/25000000000000 : ℝ), (42780017748571/100000000000000 : ℝ), (54365954639/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344695841/10000000000 : ℝ)|^8369 ≤ (10907123395139/25000000000000 : ℝ)^6321
        have hw : |(5344695841/10000000000 : ℝ)|=(5344695841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266001213/10000000000 : ℝ)|^8369 ≤ (42780017748571/100000000000000 : ℝ)^6321
        have hw : |(5266001213/10000000000 : ℝ)|=(5266001213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553742097/2500000000 : ℝ)|^8369 ≤ (54365954639/400000000000 : ℝ)^6321
        have hw : |(-553742097/2500000000 : ℝ)|=(553742097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089972689/2500000000 : ℝ)*x 0 + (2117418343/5000000000 : ℝ)*x 1 + (561073823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089972689/2500000000 : ℝ)^8369 ≤ (6663400668931/20000000000000 : ℝ)^6321 := by
    have hnat : (1089972689 : ℕ)^8369*20000000000000^6321 ≤ 6663400668931^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089972689 2500000000 6663400668931 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117418343/5000000000 : ℝ)^8369 ≤ (32057672128669/100000000000000 : ℝ)^6321 := by
    have hnat : (2117418343 : ℕ)^8369*100000000000000^6321 ≤ 32057672128669^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117418343 5000000000 32057672128669 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561073823/1250000000 : ℝ)^8369 ≤ (1082041390923/3125000000000 : ℝ)^6321 := by
    have hnat : (561073823 : ℕ)^8369*3125000000000^6321 ≤ 1082041390923^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561073823 1250000000 1082041390923 3125000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089972689/2500000000 : ℝ), (2117418343/5000000000 : ℝ), (561073823/1250000000 : ℝ)] ![(6663400668931/20000000000000 : ℝ), (32057672128669/100000000000000 : ℝ), (1082041390923/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089972689/2500000000 : ℝ)|^8369 ≤ (6663400668931/20000000000000 : ℝ)^6321
        have hw : |(1089972689/2500000000 : ℝ)|=(1089972689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117418343/5000000000 : ℝ)|^8369 ≤ (32057672128669/100000000000000 : ℝ)^6321
        have hw : |(2117418343/5000000000 : ℝ)|=(2117418343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561073823/1250000000 : ℝ)|^8369 ≤ (1082041390923/3125000000000 : ℝ)^6321
        have hw : |(561073823/1250000000 : ℝ)|=(561073823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150711293/10000000000 : ℝ)*x 0 + (2633160811/5000000000 : ℝ)*x 1 + (2696191291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150711293/10000000000 : ℝ)^8369 ≤ (3267978208881/25000000000000 : ℝ)^6321 := by
    have hnat : (2150711293 : ℕ)^8369*25000000000000^6321 ≤ 3267978208881^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150711293 10000000000 3267978208881 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633160811/5000000000 : ℝ)^8369 ≤ (8556692815571/20000000000000 : ℝ)^6321 := by
    have hnat : (2633160811 : ℕ)^8369*20000000000000^6321 ≤ 8556692815571^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633160811 5000000000 8556692815571 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696191291/5000000000 : ℝ)^8369 ≤ (11036155764877/25000000000000 : ℝ)^6321 := by
    have hnat : (2696191291 : ℕ)^8369*25000000000000^6321 ≤ 11036155764877^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696191291 5000000000 11036155764877 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150711293/10000000000 : ℝ), (2633160811/5000000000 : ℝ), (2696191291/5000000000 : ℝ)] ![(3267978208881/25000000000000 : ℝ), (8556692815571/20000000000000 : ℝ), (11036155764877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150711293/10000000000 : ℝ)|^8369 ≤ (3267978208881/25000000000000 : ℝ)^6321
        have hw : |(-2150711293/10000000000 : ℝ)|=(2150711293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633160811/5000000000 : ℝ)|^8369 ≤ (8556692815571/20000000000000 : ℝ)^6321
        have hw : |(2633160811/5000000000 : ℝ)|=(2633160811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696191291/5000000000 : ℝ)|^8369 ≤ (11036155764877/25000000000000 : ℝ)^6321
        have hw : |(2696191291/5000000000 : ℝ)|=(2696191291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656257851/5000000000 : ℝ)*x 0 + (-1044293273/5000000000 : ℝ)*x 1 + (5392382667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656257851/5000000000 : ℝ)^8369 ≤ (676266228329/1562500000000 : ℝ)^6321 := by
    have hnat : (2656257851 : ℕ)^8369*1562500000000^6321 ≤ 676266228329^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656257851 5000000000 676266228329 1562500000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044293273/5000000000 : ℝ)^8369 ≤ (12574337382779/100000000000000 : ℝ)^6321 := by
    have hnat : (1044293273 : ℕ)^8369*100000000000000^6321 ≤ 12574337382779^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044293273 5000000000 12574337382779 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392382667/10000000000 : ℝ)^8369 ≤ (22072311990407/50000000000000 : ℝ)^6321 := by
    have hnat : (5392382667 : ℕ)^8369*50000000000000^6321 ≤ 22072311990407^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392382667 10000000000 22072311990407 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656257851/5000000000 : ℝ), (-1044293273/5000000000 : ℝ), (5392382667/10000000000 : ℝ)] ![(676266228329/1562500000000 : ℝ), (12574337382779/100000000000000 : ℝ), (22072311990407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656257851/5000000000 : ℝ)|^8369 ≤ (676266228329/1562500000000 : ℝ)^6321
        have hw : |(2656257851/5000000000 : ℝ)|=(2656257851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044293273/5000000000 : ℝ)|^8369 ≤ (12574337382779/100000000000000 : ℝ)^6321
        have hw : |(-1044293273/5000000000 : ℝ)|=(1044293273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392382667/10000000000 : ℝ)|^8369 ≤ (22072311990407/50000000000000 : ℝ)^6321
        have hw : |(5392382667/10000000000 : ℝ)|=(5392382667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312515689/10000000000 : ℝ)*x 0 + (5392382719/10000000000 : ℝ)*x 1 + (-1044293247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312515689/10000000000 : ℝ)^8369 ≤ (4328103847283/10000000000000 : ℝ)^6321 := by
    have hnat : (5312515689 : ℕ)^8369*10000000000000^6321 ≤ 4328103847283^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312515689 10000000000 4328103847283 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392382719/10000000000 : ℝ)^8369 ≤ (11036156136109/25000000000000 : ℝ)^6321 := by
    have hnat : (5392382719 : ℕ)^8369*25000000000000^6321 ≤ 11036156136109^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392382719 10000000000 11036156136109 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044293247/5000000000 : ℝ)^8369 ≤ (12574336968279/100000000000000 : ℝ)^6321 := by
    have hnat : (1044293247 : ℕ)^8369*100000000000000^6321 ≤ 12574336968279^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044293247 5000000000 12574336968279 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312515689/10000000000 : ℝ), (5392382719/10000000000 : ℝ), (-1044293247/5000000000 : ℝ)] ![(4328103847283/10000000000000 : ℝ), (11036156136109/25000000000000 : ℝ), (12574336968279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312515689/10000000000 : ℝ)|^8369 ≤ (4328103847283/10000000000000 : ℝ)^6321
        have hw : |(5312515689/10000000000 : ℝ)|=(5312515689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392382719/10000000000 : ℝ)|^8369 ≤ (11036156136109/25000000000000 : ℝ)^6321
        have hw : |(5392382719/10000000000 : ℝ)|=(5392382719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044293247/5000000000 : ℝ)|^8369 ≤ (12574336968279/100000000000000 : ℝ)^6321
        have hw : |(-1044293247/5000000000 : ℝ)|=(1044293247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s6_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359900779/10000000000 : ℝ)*x 0 + (2243974549/5000000000 : ℝ)*x 1 + (4235480233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359900779/10000000000 : ℝ)^8369 ≤ (33317104753537/100000000000000 : ℝ)^6321 := by
    have hnat : (4359900779 : ℕ)^8369*100000000000000^6321 ≤ 33317104753537^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359900779 10000000000 33317104753537 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243974549/5000000000 : ℝ)^8369 ≤ (6923754577717/20000000000000 : ℝ)^6321 := by
    have hnat : (2243974549 : ℕ)^8369*20000000000000^6321 ≤ 6923754577717^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243974549 5000000000 6923754577717 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235480233/10000000000 : ℝ)^8369 ≤ (32064122341649/100000000000000 : ℝ)^6321 := by
    have hnat : (4235480233 : ℕ)^8369*100000000000000^6321 ≤ 32064122341649^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235480233 10000000000 32064122341649 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359900779/10000000000 : ℝ), (2243974549/5000000000 : ℝ), (4235480233/10000000000 : ℝ)] ![(33317104753537/100000000000000 : ℝ), (6923754577717/20000000000000 : ℝ), (32064122341649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359900779/10000000000 : ℝ)|^8369 ≤ (33317104753537/100000000000000 : ℝ)^6321
        have hw : |(4359900779/10000000000 : ℝ)|=(4359900779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243974549/5000000000 : ℝ)|^8369 ≤ (6923754577717/20000000000000 : ℝ)^6321
        have hw : |(2243974549/5000000000 : ℝ)|=(2243974549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235480233/10000000000 : ℝ)|^8369 ≤ (32064122341649/100000000000000 : ℝ)^6321
        have hw : |(4235480233/10000000000 : ℝ)|=(4235480233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2841/25000 : ℝ) ^ (523/128 : ℝ) ≤ (432324289624467/3125000000000000000 : ℝ) := by
    have hpowers : (2841/25000 : ℝ)^523 ≤ (432324289624467/3125000000000000000 : ℝ)^128 := by
      have hnat : (2841 : ℕ)^523*3125000000000000000^128 ≤ 432324289624467^128*25000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2841 25000 432324289624467 3125000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2841/25000 : ℝ)) (X := (432324289624467/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14103/100000 : ℝ) ^ (523/128 : ℝ) ≤ (522348085391559/1562500000000000000 : ℝ) := by
    have hpowers : (14103/100000 : ℝ)^523 ≤ (522348085391559/1562500000000000000 : ℝ)^128 := by
      have hnat : (14103 : ℕ)^523*1562500000000000000^128 ≤ 522348085391559^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14103 100000 522348085391559 1562500000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14103/100000 : ℝ)) (X := (522348085391559/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562932324289624467/1562500000000000000 : ℝ) ≤ (10000677099540239/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (1562932324289624467/1562500000000000000 : ℝ)^128 ≤ (10000677099540239/10000000000000000 : ℝ)^523 := by
      have hnat : (1562932324289624467 : ℕ)^128*10000000000000000^523 ≤ 10000677099540239^523*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562932324289624467 1562500000000000000 10000677099540239 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000677099540239/10000000000000000 : ℝ)) (X := (1562932324289624467/1562500000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (625295404092081517/625000000000000000 : ℝ) ≤ (10001156557608379/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (625295404092081517/625000000000000000 : ℝ)^128 ≤ (10001156557608379/10000000000000000 : ℝ)^523 := by
      have hnat : (625295404092081517 : ℕ)^128*10000000000000000^523 ≤ 10001156557608379^523*625000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625295404092081517 625000000000000000 10001156557608379 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001156557608379/10000000000000000 : ℝ)) (X := (625295404092081517/625000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (781772348085391559/781250000000000000 : ℝ) ≤ (10001636015676519/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (781772348085391559/781250000000000000 : ℝ)^128 ≤ (10001636015676519/10000000000000000 : ℝ)^523 := by
      have hnat : (781772348085391559 : ℕ)^128*10000000000000000^523 ≤ 10001636015676519^523*781250000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781772348085391559 781250000000000000 10001636015676519 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001636015676519/10000000000000000 : ℝ)) (X := (781772348085391559/781250000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(432324289624467/3125000000000000000 : ℝ) ≤ ((9126985817556009567/9130000000000000000 : ℝ)+2*(23972903407/13695000000000 : ℝ)*(2841/25000 : ℝ))^(523/128 : ℝ) := by
    rw [show (9126985817556009567/9130000000000000000 : ℝ)+2*(23972903407/13695000000000 : ℝ)*(2841/25000 : ℝ)=(10000677099540239/10000000000000000 : ℝ) by norm_num, show 1+2*(432324289624467/3125000000000000000 : ℝ)=(1562932324289624467/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(522348085391559/1562500000000000000 : ℝ)+(432324289624467/3125000000000000000 : ℝ) ≤ ((9126985817556009567/9130000000000000000 : ℝ)+(23972903407/13695000000000 : ℝ)*((14103/100000 : ℝ)+(2841/25000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (9126985817556009567/9130000000000000000 : ℝ)+(23972903407/13695000000000 : ℝ)*((14103/100000 : ℝ)+(2841/25000 : ℝ))=(10001156557608379/10000000000000000 : ℝ) by norm_num, show 1+(522348085391559/1562500000000000000 : ℝ)+(432324289624467/3125000000000000000 : ℝ)=(625295404092081517/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(522348085391559/1562500000000000000 : ℝ) ≤ ((9126985817556009567/9130000000000000000 : ℝ)+2*(23972903407/13695000000000 : ℝ)*(14103/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (9126985817556009567/9130000000000000000 : ℝ)+2*(23972903407/13695000000000 : ℝ)*(14103/100000 : ℝ)=(10001636015676519/10000000000000000 : ℝ) by norm_num, show 1+2*(522348085391559/1562500000000000000 : ℝ)=(781772348085391559/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9126985817556009567/9130000000000000000 : ℝ)*(X 1 0+X 2 0)+(23972903407/13695000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (9126985817556009567/9130000000000000000 : ℝ)) (alpha := (23972903407/13695000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9126985817556009567/9130000000000000000 : ℝ)*(X 0 1+X 2 1)+(23972903407/13695000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (9126985817556009567/9130000000000000000 : ℝ)) (alpha := (23972903407/13695000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9126985817556009567/9130000000000000000 : ℝ)*(X 0 2+X 1 2)+(23972903407/13695000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (9126985817556009567/9130000000000000000 : ℝ)) (alpha := (23972903407/13695000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150706583/10000000000 : ℝ)*X 0 0+(5392703643/10000000000 : ℝ)*X 0 1+(526600161/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668086979/1250000000 : ℝ)*X 1 0+(-442993461/2000000000 : ℝ)*X 1 1+(5266002039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344695841/10000000000 : ℝ)*X 2 0+(5266001213/10000000000 : ℝ)*X 2 1+(-553742097/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089972689/2500000000 : ℝ)*X 0 0+(2117418343/5000000000 : ℝ)*X 0 1+(561073823/1250000000 : ℝ)*X 0 2+(1089972689/2500000000 : ℝ)*X 1 0+(2117418343/5000000000 : ℝ)*X 1 1+(561073823/1250000000 : ℝ)*X 1 2+(1089972689/2500000000 : ℝ)*X 2 0+(2117418343/5000000000 : ℝ)*X 2 1+(561073823/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2150711293/10000000000 : ℝ)*X 0 0+(2633160811/5000000000 : ℝ)*X 0 1+(2696191291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656257851/5000000000 : ℝ)*X 1 0+(-1044293273/5000000000 : ℝ)*X 1 1+(5392382667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312515689/10000000000 : ℝ)*X 2 0+(5392382719/10000000000 : ℝ)*X 2 1+(-1044293247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359900779/10000000000 : ℝ)*X 0 0+(2243974549/5000000000 : ℝ)*X 0 1+(4235480233/10000000000 : ℝ)*X 0 2+(4359900779/10000000000 : ℝ)*X 1 0+(2243974549/5000000000 : ℝ)*X 1 1+(4235480233/10000000000 : ℝ)*X 1 2+(4359900779/10000000000 : ℝ)*X 2 0+(2243974549/5000000000 : ℝ)*X 2 1+(4235480233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3567716292275162685082132509/456500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102702951/20000000000000 : ℝ)*(base19) + (466967127/100000000000000 : ℝ)*(base23) + (131907471/100000000000000 : ℝ)*(upper2) + (78686161/25000000000000 : ℝ)*(upper3) + (5916738754834209/100000000000000 : ℝ)*(major0) + (5916738754834209/100000000000000 : ℝ)*(major1) + (5916738754834209/100000000000000 : ℝ)*(major2) + (789257664821981/10000000000000 : ℝ)*(sp0) + (493287328562317/6250000000000 : ℝ)*(sp1) + (7892546374916763/100000000000000 : ℝ)*(sp2) + (1970425454728679/50000000000000 : ℝ)*(sp3) + (21122292017/100000000000000 : ℝ)*(sp4) + (50928627937/100000000000000 : ℝ)*(sp6) + (14284593449/50000000000000 : ℝ)*(sp7) + (123152483707633/3125000000000 : ℝ)*(f.failure) + (7892597770511827/100000000000000 : ℝ)*(f.sum) + (1232837827743/913000000000000000000000000 : ℝ)*base66 + (570270175396877503/913000000000000000000000000000000 : ℝ)*base67 + (9140702131155122497/913000000000000000000000000000000 : ℝ)*base70 + (6243773514922877503/913000000000000000000000000000000 : ℝ)*base71 + (769115515733/228250000000000000000000000 : ℝ)*base74 + (18897648105337122497/913000000000000000000000000000000 : ℝ)*base76 + (3734296090713122497/913000000000000000000000000000000 : ℝ)*base78 + (29024254893437122497/913000000000000000000000000000000 : ℝ)*base80 + (1490730344877/228250000000000000000000000 : ℝ)*base82 + (4272793/312500000000000000000 : ℝ)*base89 + (4272793/312500000000000000000 : ℝ)*base91 + (4272793/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7806247454891327202551/913000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1217283963/100000000000000 : ℝ)*(base19) + (367359361/25000000000000 : ℝ)*(base23) + (6221373/3125000000000 : ℝ)*(upper3) + (13262179/12500000000000 : ℝ)*(lower4) + (128600399/100000000000000 : ℝ)*(upper5) + (743346821898181/12500000000000 : ℝ)*(major0) + (743346821898181/12500000000000 : ℝ)*(major1) + (743346821898181/12500000000000 : ℝ)*(major2) + (1061331501/3125000000000 : ℝ)*(sp1) + (45824542789/100000000000000 : ℝ)*(sp2) + (3966331923850231/50000000000000 : ℝ)*(sp4) + (7932628667808467/100000000000000 : ℝ)*(sp5) + (793261655372023/10000000000000 : ℝ)*(sp6) + (990221254416717/25000000000000 : ℝ)*(sp7) + (990221254416717/25000000000000 : ℝ)*(f.failure) + (3966331923850231/50000000000000 : ℝ)*(f.sum) + (264475043029/273900000000000000000000000 : ℝ)*base66 + (1587243269744807119/342375000000000000000000000000000 : ℝ)*base68 + (5645086675342692881/342375000000000000000000000000000 : ℝ)*base69 + (286374061970442881/342375000000000000000000000000000 : ℝ)*base71 + (4831901815307/1369500000000000000000000000 : ℝ)*base74 + (2076930096078182119/342375000000000000000000000000000 : ℝ)*base76 + (991544142023067881/342375000000000000000000000000000 : ℝ)*base77 + (4136950658939432119/342375000000000000000000000000000 : ℝ)*base80 + (3227425687439/684750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8661443/2500000000000000000000 : ℝ)*base90 + (8661443/2500000000000000000000 : ℝ)*base92 + (8661443/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1176_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s7_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33605147/156250000 : ℝ)*x 0 + (5392431227/10000000000 : ℝ)*x 1 + (5266259051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33605147/156250000 : ℝ)^8369 ≤ (6536029305377/50000000000000 : ℝ)^6321 := by
    have hnat : (33605147 : ℕ)^8369*50000000000000^6321 ≤ 6536029305377^6321*156250000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33605147 156250000 6536029305377 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392431227/10000000000 : ℝ)^8369 ≤ (8829030063637/20000000000000 : ℝ)^6321 := by
    have hnat : (5392431227 : ℕ)^8369*20000000000000^6321 ≤ 8829030063637^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392431227 10000000000 8829030063637 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266259051/10000000000 : ℝ)^8369 ≤ (5347848882109/12500000000000 : ℝ)^6321 := by
    have hnat : (5266259051 : ℕ)^8369*12500000000000^6321 ≤ 5347848882109^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266259051 10000000000 5347848882109 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33605147/156250000 : ℝ), (5392431227/10000000000 : ℝ), (5266259051/10000000000 : ℝ)] ![(6536029305377/50000000000000 : ℝ), (8829030063637/20000000000000 : ℝ), (5347848882109/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33605147/156250000 : ℝ)|^8369 ≤ (6536029305377/50000000000000 : ℝ)^6321
        have hw : |(-33605147/156250000 : ℝ)|=(33605147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392431227/10000000000 : ℝ)|^8369 ≤ (8829030063637/20000000000000 : ℝ)^6321
        have hw : |(5392431227/10000000000 : ℝ)|=(5392431227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266259051/10000000000 : ℝ)|^8369 ≤ (5347848882109/12500000000000 : ℝ)^6321
        have hw : |(5266259051/10000000000 : ℝ)|=(5266259051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068925453/2000000000 : ℝ)*x 0 + (-442943601/2000000000 : ℝ)*x 1 + (1316564809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068925453/2000000000 : ℝ)^8369 ≤ (43627752430327/100000000000000 : ℝ)^6321 := by
    have hnat : (1068925453 : ℕ)^8369*100000000000000^6321 ≤ 43627752430327^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068925453 2000000000 43627752430327 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442943601/2000000000 : ℝ)^8369 ≤ (13589454504211/100000000000000 : ℝ)^6321 := by
    have hnat : (442943601 : ℕ)^8369*100000000000000^6321 ≤ 13589454504211^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442943601 2000000000 13589454504211 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316564809/2500000000 : ℝ)^8369 ≤ (171131172187/400000000000 : ℝ)^6321 := by
    have hnat : (1316564809 : ℕ)^8369*400000000000^6321 ≤ 171131172187^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316564809 2500000000 171131172187 400000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068925453/2000000000 : ℝ), (-442943601/2000000000 : ℝ), (1316564809/2500000000 : ℝ)] ![(43627752430327/100000000000000 : ℝ), (13589454504211/100000000000000 : ℝ), (171131172187/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068925453/2000000000 : ℝ)|^8369 ≤ (43627752430327/100000000000000 : ℝ)^6321
        have hw : |(1068925453/2000000000 : ℝ)|=(1068925453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442943601/2000000000 : ℝ)|^8369 ≤ (13589454504211/100000000000000 : ℝ)^6321
        have hw : |(-442943601/2000000000 : ℝ)|=(442943601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316564809/2500000000 : ℝ)|^8369 ≤ (171131172187/400000000000 : ℝ)^6321
        have hw : |(1316564809/2500000000 : ℝ)|=(1316564809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672313689/5000000000 : ℝ)*x 0 + (5266259279/10000000000 : ℝ)*x 1 + (-2214717799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672313689/5000000000 : ℝ)^8369 ≤ (43627753651597/100000000000000 : ℝ)^6321 := by
    have hnat : (2672313689 : ℕ)^8369*100000000000000^6321 ≤ 43627753651597^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672313689 5000000000 43627753651597 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266259279/10000000000 : ℝ)^8369 ≤ (21391396754631/50000000000000 : ℝ)^6321 := by
    have hnat : (5266259279 : ℕ)^8369*50000000000000^6321 ≤ 21391396754631^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266259279 10000000000 21391396754631 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214717799/10000000000 : ℝ)^8369 ≤ (6794726415331/50000000000000 : ℝ)^6321 := by
    have hnat : (2214717799 : ℕ)^8369*50000000000000^6321 ≤ 6794726415331^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214717799 10000000000 6794726415331 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672313689/5000000000 : ℝ), (5266259279/10000000000 : ℝ), (-2214717799/10000000000 : ℝ)] ![(43627753651597/100000000000000 : ℝ), (21391396754631/50000000000000 : ℝ), (6794726415331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672313689/5000000000 : ℝ)|^8369 ≤ (43627753651597/100000000000000 : ℝ)^6321
        have hw : |(2672313689/5000000000 : ℝ)|=(2672313689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266259279/10000000000 : ℝ)|^8369 ≤ (21391396754631/50000000000000 : ℝ)^6321
        have hw : |(5266259279/10000000000 : ℝ)|=(5266259279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214717799/10000000000 : ℝ)|^8369 ≤ (6794726415331/50000000000000 : ℝ)^6321
        have hw : |(-2214717799/10000000000 : ℝ)|=(2214717799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359904857/10000000000 : ℝ)*x 0 + (4235365843/10000000000 : ℝ)*x 1 + (4488057321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359904857/10000000000 : ℝ)^8369 ≤ (8329286503301/25000000000000 : ℝ)^6321 := by
    have hnat : (4359904857 : ℕ)^8369*25000000000000^6321 ≤ 8329286503301^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359904857 10000000000 8329286503301 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235365843/10000000000 : ℝ)^8369 ≤ (32062975797889/100000000000000 : ℝ)^6321 := by
    have hnat : (4235365843 : ℕ)^8369*100000000000000^6321 ≤ 32062975797889^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235365843 10000000000 32062975797889 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488057321/10000000000 : ℝ)^8369 ≤ (17309939084901/50000000000000 : ℝ)^6321 := by
    have hnat : (4488057321 : ℕ)^8369*50000000000000^6321 ≤ 17309939084901^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488057321 10000000000 17309939084901 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359904857/10000000000 : ℝ), (4235365843/10000000000 : ℝ), (4488057321/10000000000 : ℝ)] ![(8329286503301/25000000000000 : ℝ), (32062975797889/100000000000000 : ℝ), (17309939084901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359904857/10000000000 : ℝ)|^8369 ≤ (8329286503301/25000000000000 : ℝ)^6321
        have hw : |(4359904857/10000000000 : ℝ)|=(4359904857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235365843/10000000000 : ℝ)|^8369 ≤ (32062975797889/100000000000000 : ℝ)^6321
        have hw : |(4235365843/10000000000 : ℝ)|=(4235365843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488057321/10000000000 : ℝ)|^8369 ≤ (17309939084901/50000000000000 : ℝ)^6321
        have hw : |(4488057321/10000000000 : ℝ)|=(4488057321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150733957/10000000000 : ℝ)*x 0 + (2633288279/5000000000 : ℝ)*x 1 + (2696056381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150733957/10000000000 : ℝ)^8369 ≤ (13072095217581/100000000000000 : ℝ)^6321 := by
    have hnat : (2150733957 : ℕ)^8369*100000000000000^6321 ≤ 13072095217581^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150733957 10000000000 13072095217581 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633288279/5000000000 : ℝ)^8369 ≤ (42786206226023/100000000000000 : ℝ)^6321 := by
    have hnat : (2633288279 : ℕ)^8369*100000000000000^6321 ≤ 42786206226023^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633288279 5000000000 42786206226023 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696056381/5000000000 : ℝ)^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321 := by
    have hnat : (2696056381 : ℕ)^8369*100000000000000^6321 ≤ 44141698533347^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696056381 5000000000 44141698533347 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150733957/10000000000 : ℝ), (2633288279/5000000000 : ℝ), (2696056381/5000000000 : ℝ)] ![(13072095217581/100000000000000 : ℝ), (42786206226023/100000000000000 : ℝ), (44141698533347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150733957/10000000000 : ℝ)|^8369 ≤ (13072095217581/100000000000000 : ℝ)^6321
        have hw : |(-2150733957/10000000000 : ℝ)|=(2150733957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633288279/5000000000 : ℝ)|^8369 ≤ (42786206226023/100000000000000 : ℝ)^6321
        have hw : |(2633288279/5000000000 : ℝ)|=(2633288279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696056381/5000000000 : ℝ)|^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321
        have hw : |(2696056381/5000000000 : ℝ)|=(2696056381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664072731/1250000000 : ℝ)*x 0 + (-522216009/2500000000 : ℝ)*x 1 + (2696056381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664072731/1250000000 : ℝ)^8369 ≤ (43281752106007/100000000000000 : ℝ)^6321 := by
    have hnat : (664072731 : ℕ)^8369*100000000000000^6321 ≤ 43281752106007^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664072731 1250000000 43281752106007 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522216009/2500000000 : ℝ)^8369 ≤ (196508583467/1562500000000 : ℝ)^6321 := by
    have hnat : (522216009 : ℕ)^8369*1562500000000^6321 ≤ 196508583467^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522216009 2500000000 196508583467 1562500000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696056381/5000000000 : ℝ)^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321 := by
    have hnat : (2696056381 : ℕ)^8369*100000000000000^6321 ≤ 44141698533347^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696056381 5000000000 44141698533347 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664072731/1250000000 : ℝ), (-522216009/2500000000 : ℝ), (2696056381/5000000000 : ℝ)] ![(43281752106007/100000000000000 : ℝ), (196508583467/1562500000000 : ℝ), (44141698533347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664072731/1250000000 : ℝ)|^8369 ≤ (43281752106007/100000000000000 : ℝ)^6321
        have hw : |(664072731/1250000000 : ℝ)|=(664072731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522216009/2500000000 : ℝ)|^8369 ≤ (196508583467/1562500000000 : ℝ)^6321
        have hw : |(-522216009/2500000000 : ℝ)|=(522216009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696056381/5000000000 : ℝ)|^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321
        have hw : |(2696056381/5000000000 : ℝ)|=(2696056381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664072731/1250000000 : ℝ)*x 0 + (2696056381/5000000000 : ℝ)*x 1 + (-522216009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664072731/1250000000 : ℝ)^8369 ≤ (43281752106007/100000000000000 : ℝ)^6321 := by
    have hnat : (664072731 : ℕ)^8369*100000000000000^6321 ≤ 43281752106007^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664072731 1250000000 43281752106007 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696056381/5000000000 : ℝ)^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321 := by
    have hnat : (2696056381 : ℕ)^8369*100000000000000^6321 ≤ 44141698533347^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696056381 5000000000 44141698533347 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522216009/2500000000 : ℝ)^8369 ≤ (196508583467/1562500000000 : ℝ)^6321 := by
    have hnat : (522216009 : ℕ)^8369*1562500000000^6321 ≤ 196508583467^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522216009 2500000000 196508583467 1562500000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664072731/1250000000 : ℝ), (2696056381/5000000000 : ℝ), (-522216009/2500000000 : ℝ)] ![(43281752106007/100000000000000 : ℝ), (44141698533347/100000000000000 : ℝ), (196508583467/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664072731/1250000000 : ℝ)|^8369 ≤ (43281752106007/100000000000000 : ℝ)^6321
        have hw : |(664072731/1250000000 : ℝ)|=(664072731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696056381/5000000000 : ℝ)|^8369 ≤ (44141698533347/100000000000000 : ℝ)^6321
        have hw : |(2696056381/5000000000 : ℝ)|=(2696056381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522216009/2500000000 : ℝ)|^8369 ≤ (196508583467/1562500000000 : ℝ)^6321
        have hw : |(-522216009/2500000000 : ℝ)|=(522216009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s7_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871982819/2000000000 : ℝ)*x 0 + (448742177/1000000000 : ℝ)*x 1 + (847200817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871982819/2000000000 : ℝ)^8369 ≤ (33317239479851/100000000000000 : ℝ)^6321 := by
    have hnat : (871982819 : ℕ)^8369*100000000000000^6321 ≤ 33317239479851^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871982819 2000000000 33317239479851 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448742177/1000000000 : ℝ)^8369 ≤ (4326673426581/12500000000000 : ℝ)^6321 := by
    have hnat : (448742177 : ℕ)^8369*12500000000000^6321 ≤ 4326673426581^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448742177 1000000000 4326673426581 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847200817/2000000000 : ℝ)^8369 ≤ (1002167909281/3125000000000 : ℝ)^6321 := by
    have hnat : (847200817 : ℕ)^8369*3125000000000^6321 ≤ 1002167909281^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847200817 2000000000 1002167909281 3125000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871982819/2000000000 : ℝ), (448742177/1000000000 : ℝ), (847200817/2000000000 : ℝ)] ![(33317239479851/100000000000000 : ℝ), (4326673426581/12500000000000 : ℝ), (1002167909281/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871982819/2000000000 : ℝ)|^8369 ≤ (33317239479851/100000000000000 : ℝ)^6321
        have hw : |(871982819/2000000000 : ℝ)|=(871982819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448742177/1000000000 : ℝ)|^8369 ≤ (4326673426581/12500000000000 : ℝ)^6321
        have hw : |(448742177/1000000000 : ℝ)|=(448742177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847200817/2000000000 : ℝ)|^8369 ≤ (1002167909281/3125000000000 : ℝ)^6321
        have hw : |(847200817/2000000000 : ℝ)|=(847200817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11391/100000 : ℝ) ^ (523/128 : ℝ) ≤ (6984586431103131/50000000000000000000 : ℝ) := by
    have hpowers : (11391/100000 : ℝ)^523 ≤ (6984586431103131/50000000000000000000 : ℝ)^128 := by
      have hnat : (11391 : ℕ)^523*50000000000000000000^128 ≤ 6984586431103131^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 100000 6984586431103131 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/100000 : ℝ)) (X := (6984586431103131/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (523/128 : ℝ) ≤ (33159914246718471/100000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^523 ≤ (33159914246718471/100000000000000000000 : ℝ)^128 := by
      have hnat : (563 : ℕ)^523*100000000000000000000^128 ≤ 33159914246718471^128*4000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 33159914246718471 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (33159914246718471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006984586431103131/25000000000000000000 : ℝ) ≤ (10000683696180329/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25006984586431103131/25000000000000000000 : ℝ)^128 ≤ (10000683696180329/10000000000000000 : ℝ)^523 := by
      have hnat : (25006984586431103131 : ℕ)^128*10000000000000000^523 ≤ 10000683696180329^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006984586431103131 25000000000000000000 10000683696180329 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683696180329/10000000000000000 : ℝ)) (X := (25006984586431103131/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047129087108924733/100000000000000000000 : ℝ) ≤ (10001153240883149/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (100047129087108924733/100000000000000000000 : ℝ)^128 ≤ (10001153240883149/10000000000000000 : ℝ)^523 := by
      have hnat : (100047129087108924733 : ℕ)^128*10000000000000000^523 ≤ 10001153240883149^523*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047129087108924733 100000000000000000000 10001153240883149 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001153240883149/10000000000000000 : ℝ)) (X := (100047129087108924733/100000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033159914246718471/50000000000000000000 : ℝ) ≤ (10001622785585969/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50033159914246718471/50000000000000000000 : ℝ)^128 ≤ (10001622785585969/10000000000000000 : ℝ)^523 := by
      have hnat : (50033159914246718471 : ℕ)^128*10000000000000000^523 ≤ 10001622785585969^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033159914246718471 50000000000000000000 10001622785585969 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001622785585969/10000000000000000 : ℝ)) (X := (50033159914246718471/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6984586431103131/50000000000000000000 : ℝ) ≤ ((6707784468282089449/6710000000000000000 : ℝ)+2*(23477235141/13420000000000 : ℝ)*(11391/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (6707784468282089449/6710000000000000000 : ℝ)+2*(23477235141/13420000000000 : ℝ)*(11391/100000 : ℝ)=(10000683696180329/10000000000000000 : ℝ) by norm_num, show 1+2*(6984586431103131/50000000000000000000 : ℝ)=(25006984586431103131/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33159914246718471/100000000000000000000 : ℝ)+(6984586431103131/50000000000000000000 : ℝ) ≤ ((6707784468282089449/6710000000000000000 : ℝ)+(23477235141/13420000000000 : ℝ)*((563/4000 : ℝ)+(11391/100000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (6707784468282089449/6710000000000000000 : ℝ)+(23477235141/13420000000000 : ℝ)*((563/4000 : ℝ)+(11391/100000 : ℝ))=(10001153240883149/10000000000000000 : ℝ) by norm_num, show 1+(33159914246718471/100000000000000000000 : ℝ)+(6984586431103131/50000000000000000000 : ℝ)=(100047129087108924733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33159914246718471/100000000000000000000 : ℝ) ≤ ((6707784468282089449/6710000000000000000 : ℝ)+2*(23477235141/13420000000000 : ℝ)*(563/4000 : ℝ))^(523/128 : ℝ) := by
    rw [show (6707784468282089449/6710000000000000000 : ℝ)+2*(23477235141/13420000000000 : ℝ)*(563/4000 : ℝ)=(10001622785585969/10000000000000000 : ℝ) by norm_num, show 1+2*(33159914246718471/100000000000000000000 : ℝ)=(50033159914246718471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6707784468282089449/6710000000000000000 : ℝ)*(X 1 0+X 2 0)+(23477235141/13420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (6707784468282089449/6710000000000000000 : ℝ)) (alpha := (23477235141/13420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6707784468282089449/6710000000000000000 : ℝ)*(X 0 1+X 2 1)+(23477235141/13420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (6707784468282089449/6710000000000000000 : ℝ)) (alpha := (23477235141/13420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6707784468282089449/6710000000000000000 : ℝ)*(X 0 2+X 1 2)+(23477235141/13420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (6707784468282089449/6710000000000000000 : ℝ)) (alpha := (23477235141/13420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-33605147/156250000 : ℝ)*X 0 0+(5392431227/10000000000 : ℝ)*X 0 1+(5266259051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068925453/2000000000 : ℝ)*X 1 0+(-442943601/2000000000 : ℝ)*X 1 1+(1316564809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672313689/5000000000 : ℝ)*X 2 0+(5266259279/10000000000 : ℝ)*X 2 1+(-2214717799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359904857/10000000000 : ℝ)*X 0 0+(4235365843/10000000000 : ℝ)*X 0 1+(4488057321/10000000000 : ℝ)*X 0 2+(4359904857/10000000000 : ℝ)*X 1 0+(4235365843/10000000000 : ℝ)*X 1 1+(4488057321/10000000000 : ℝ)*X 1 2+(4359904857/10000000000 : ℝ)*X 2 0+(4235365843/10000000000 : ℝ)*X 2 1+(4488057321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2150733957/10000000000 : ℝ)*X 0 0+(2633288279/5000000000 : ℝ)*X 0 1+(2696056381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664072731/1250000000 : ℝ)*X 1 0+(-522216009/2500000000 : ℝ)*X 1 1+(2696056381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664072731/1250000000 : ℝ)*X 2 0+(2696056381/5000000000 : ℝ)*X 2 1+(-522216009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871982819/2000000000 : ℝ)*X 0 0+(448742177/1000000000 : ℝ)*X 0 1+(847200817/2000000000 : ℝ)*X 0 2+(871982819/2000000000 : ℝ)*X 1 0+(448742177/1000000000 : ℝ)*X 1 1+(847200817/2000000000 : ℝ)*X 1 2+(871982819/2000000000 : ℝ)*X 2 0+(448742177/1000000000 : ℝ)*X 2 1+(847200817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3677979478120599193148365311/335500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21427297/1250000000000 : ℝ)*(base19) + (1828391363/100000000000000 : ℝ)*(base23) + (28521503/100000000000000 : ℝ)*(lower2) + (9613183/4000000000000 : ℝ)*(upper3) + (141536353/25000000000000 : ℝ)*(upper5) + (5941608582651471/100000000000000 : ℝ)*(major0) + (5941608582651471/100000000000000 : ℝ)*(major1) + (5941608582651471/100000000000000 : ℝ)*(major2) + (1981428898089947/25000000000000 : ℝ)*(sp0) + (7925770908466801/100000000000000 : ℝ)*(sp1) + (3962885397129599/50000000000000 : ℝ)*(sp2) + (989355566458811/25000000000000 : ℝ)*(sp3) + (57030290773/100000000000000 : ℝ)*(sp4) + (10955697213/50000000000000 : ℝ)*(sp7) + (989361044307417/25000000000000 : ℝ)*(f.failure) + (7925772622650561/100000000000000 : ℝ)*(f.sum) + (1754730014403/167750000000000000000000000 : ℝ)*base66 + (3776410328043070521/671000000000000000000000000000000 : ℝ)*base68 + (6185980605289070521/671000000000000000000000000000000 : ℝ)*base70 + (3902772995034070521/671000000000000000000000000000000 : ℝ)*base72 + (227156971993/335500000000000000000000000 : ℝ)*base74 + (1957363983851070521/671000000000000000000000000000000 : ℝ)*base76 + (4498079886543070521/671000000000000000000000000000000 : ℝ)*base78 + (8448448478515070521/671000000000000000000000000000000 : ℝ)*base80 + (2664194486361/671000000000000000000000000 : ℝ)*base82 + (24706743/2500000000000000000000 : ℝ)*base90 + (24706743/2500000000000000000000 : ℝ)*base92 + (24706743/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3529943310655539374451/671000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119758257/12500000000000 : ℝ)*(base19) + (520889383/50000000000000 : ℝ)*(base23) + (6616851/6250000000000 : ℝ)*(upper3) + (19052063/50000000000000 : ℝ)*(lower4) + (107844551/100000000000000 : ℝ)*(upper5) + (2985818335279409/50000000000000 : ℝ)*(major0) + (2985818335279409/50000000000000 : ℝ)*(major1) + (2985818335279409/50000000000000 : ℝ)*(major2) + (26665634997/100000000000000 : ℝ)*(sp1) + (179081291/625000000000 : ℝ)*(sp2) + (7965828599748821/100000000000000 : ℝ)*(sp4) + (995725122005971/12500000000000 : ℝ)*(sp5) + (7965798904963493/100000000000000 : ℝ)*(sp6) + (1988722283005731/50000000000000 : ℝ)*(sp7) + (1988722283005731/50000000000000 : ℝ)*(f.failure) + (7965828599748821/100000000000000 : ℝ)*(f.sum) + (705657162367/134200000000000000000000000 : ℝ)*base65 + (2215352138221355641/335500000000000000000000000000000 : ℝ)*base67 + (1071343421475644359/335500000000000000000000000000000 : ℝ)*base70 + (1486512105635855641/335500000000000000000000000000000 : ℝ)*base71 + (890522466541/671000000000000000000000000 : ℝ)*base73 + (2816595601938644359/335500000000000000000000000000000 : ℝ)*base76 + (3224567579626644359/335500000000000000000000000000000 : ℝ)*base78 + (6164009394347355641/335500000000000000000000000000000 : ℝ)*base79 + (989015283829/167750000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base88 + (18867149/5000000000000000000000 : ℝ)*base90 + (18867149/5000000000000000000000 : ℝ)*base92 + (18867149/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1176_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s8_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-134421011/625000000 : ℝ)*x 0 + (1078475241/2000000000 : ℝ)*x 1 + (5266309433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134421011/625000000 : ℝ)^8369 ≤ (6536056537191/50000000000000 : ℝ)^6321 := by
    have hnat : (134421011 : ℕ)^8369*50000000000000^6321 ≤ 6536056537191^6321*625000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134421011 625000000 6536056537191 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078475241/2000000000 : ℝ)^8369 ≤ (22072276969953/50000000000000 : ℝ)^6321 := by
    have hnat : (1078475241 : ℕ)^8369*50000000000000^6321 ≤ 22072276969953^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078475241 2000000000 22072276969953 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266309433/10000000000 : ℝ)^8369 ≤ (2673958310709/6250000000000 : ℝ)^6321 := by
    have hnat : (5266309433 : ℕ)^8369*6250000000000^6321 ≤ 2673958310709^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266309433 10000000000 2673958310709 6250000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134421011/625000000 : ℝ), (1078475241/2000000000 : ℝ), (5266309433/10000000000 : ℝ)] ![(6536056537191/50000000000000 : ℝ), (22072276969953/50000000000000 : ℝ), (2673958310709/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134421011/625000000 : ℝ)|^8369 ≤ (6536056537191/50000000000000 : ℝ)^6321
        have hw : |(-134421011/625000000 : ℝ)|=(134421011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078475241/2000000000 : ℝ)|^8369 ≤ (22072276969953/50000000000000 : ℝ)^6321
        have hw : |(1078475241/2000000000 : ℝ)|=(1078475241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266309433/10000000000 : ℝ)|^8369 ≤ (2673958310709/6250000000000 : ℝ)^6321
        have hw : |(5266309433/10000000000 : ℝ)|=(5266309433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344613041/10000000000 : ℝ)*x 0 + (-2214670447/10000000000 : ℝ)*x 1 + (5266309449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344613041/10000000000 : ℝ)^8369 ≤ (43627598701699/100000000000000 : ℝ)^6321 := by
    have hnat : (5344613041 : ℕ)^8369*100000000000000^6321 ≤ 43627598701699^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344613041 10000000000 43627598701699 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214670447/10000000000 : ℝ)^8369 ≤ (13589068143073/100000000000000 : ℝ)^6321 := by
    have hnat : (2214670447 : ℕ)^8369*100000000000000^6321 ≤ 13589068143073^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214670447 10000000000 13589068143073 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266309449/10000000000 : ℝ)^8369 ≤ (21391666571721/50000000000000 : ℝ)^6321 := by
    have hnat : (5266309449 : ℕ)^8369*50000000000000^6321 ≤ 21391666571721^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266309449 10000000000 21391666571721 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344613041/10000000000 : ℝ), (-2214670447/10000000000 : ℝ), (5266309449/10000000000 : ℝ)] ![(43627598701699/100000000000000 : ℝ), (13589068143073/100000000000000 : ℝ), (21391666571721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344613041/10000000000 : ℝ)|^8369 ≤ (43627598701699/100000000000000 : ℝ)^6321
        have hw : |(5344613041/10000000000 : ℝ)|=(5344613041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214670447/10000000000 : ℝ)|^8369 ≤ (13589068143073/100000000000000 : ℝ)^6321
        have hw : |(-2214670447/10000000000 : ℝ)|=(2214670447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266309449/10000000000 : ℝ)|^8369 ≤ (21391666571721/50000000000000 : ℝ)^6321
        have hw : |(5266309449/10000000000 : ℝ)|=(5266309449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672306519/5000000000 : ℝ)*x 0 + (1053261889/2000000000 : ℝ)*x 1 + (-2214670457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672306519/5000000000 : ℝ)^8369 ≤ (10906899667319/25000000000000 : ℝ)^6321 := by
    have hnat : (2672306519 : ℕ)^8369*25000000000000^6321 ≤ 10906899667319^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672306519 5000000000 10906899667319 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053261889/2000000000 : ℝ)^8369 ≤ (21391666550209/50000000000000 : ℝ)^6321 := by
    have hnat : (1053261889 : ℕ)^8369*50000000000000^6321 ≤ 21391666550209^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053261889 2000000000 21391666550209 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214670457/10000000000 : ℝ)^8369 ≤ (13589068224313/100000000000000 : ℝ)^6321 := by
    have hnat : (2214670457 : ℕ)^8369*100000000000000^6321 ≤ 13589068224313^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214670457 10000000000 13589068224313 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672306519/5000000000 : ℝ), (1053261889/2000000000 : ℝ), (-2214670457/10000000000 : ℝ)] ![(10906899667319/25000000000000 : ℝ), (21391666550209/50000000000000 : ℝ), (13589068224313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672306519/5000000000 : ℝ)|^8369 ≤ (10906899667319/25000000000000 : ℝ)^6321
        have hw : |(2672306519/5000000000 : ℝ)|=(2672306519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053261889/2000000000 : ℝ)|^8369 ≤ (21391666550209/50000000000000 : ℝ)^6321
        have hw : |(1053261889/2000000000 : ℝ)|=(1053261889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214670457/10000000000 : ℝ)|^8369 ≤ (13589068224313/100000000000000 : ℝ)^6321
        have hw : |(-2214670457/10000000000 : ℝ)|=(2214670457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359907147/10000000000 : ℝ)*x 0 + (529433913/1250000000 : ℝ)*x 1 + (70124243/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359907147/10000000000 : ℝ)^8369 ≤ (16658584591283/50000000000000 : ℝ)^6321 := by
    have hnat : (4359907147 : ℕ)^8369*50000000000000^6321 ≤ 16658584591283^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359907147 10000000000 16658584591283 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529433913/1250000000 : ℝ)^8369 ≤ (32064032844923/100000000000000 : ℝ)^6321 := by
    have hnat : (529433913 : ℕ)^8369*100000000000000^6321 ≤ 32064032844923^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529433913 1250000000 32064032844923 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70124243/156250000 : ℝ)^8369 ≤ (2163674871949/6250000000000 : ℝ)^6321 := by
    have hnat : (70124243 : ℕ)^8369*6250000000000^6321 ≤ 2163674871949^6321*156250000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70124243 156250000 2163674871949 6250000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359907147/10000000000 : ℝ), (529433913/1250000000 : ℝ), (70124243/156250000 : ℝ)] ![(16658584591283/50000000000000 : ℝ), (32064032844923/100000000000000 : ℝ), (2163674871949/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359907147/10000000000 : ℝ)|^8369 ≤ (16658584591283/50000000000000 : ℝ)^6321
        have hw : |(4359907147/10000000000 : ℝ)|=(4359907147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529433913/1250000000 : ℝ)|^8369 ≤ (32064032844923/100000000000000 : ℝ)^6321
        have hw : |(529433913/1250000000 : ℝ)|=(529433913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70124243/156250000 : ℝ)|^8369 ≤ (2163674871949/6250000000000 : ℝ)^6321
        have hw : |(70124243/156250000 : ℝ)|=(70124243/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268842591/1250000000 : ℝ)*x 0 + (658328233/1250000000 : ℝ)*x 1 + (1348014701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268842591/1250000000 : ℝ)^8369 ≤ (13072149705387/100000000000000 : ℝ)^6321 := by
    have hnat : (268842591 : ℕ)^8369*100000000000000^6321 ≤ 13072149705387^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268842591 1250000000 13072149705387 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658328233/1250000000 : ℝ)^8369 ≤ (2139336828863/5000000000000 : ℝ)^6321 := by
    have hnat : (658328233 : ℕ)^8369*5000000000000^6321 ≤ 2139336828863^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658328233 1250000000 2139336828863 5000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348014701/2500000000 : ℝ)^8369 ≤ (11035278424709/25000000000000 : ℝ)^6321 := by
    have hnat : (1348014701 : ℕ)^8369*25000000000000^6321 ≤ 11035278424709^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348014701 2500000000 11035278424709 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268842591/1250000000 : ℝ), (658328233/1250000000 : ℝ), (1348014701/2500000000 : ℝ)] ![(13072149705387/100000000000000 : ℝ), (2139336828863/5000000000000 : ℝ), (11035278424709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268842591/1250000000 : ℝ)|^8369 ≤ (13072149705387/100000000000000 : ℝ)^6321
        have hw : |(-268842591/1250000000 : ℝ)|=(268842591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658328233/1250000000 : ℝ)|^8369 ≤ (2139336828863/5000000000000 : ℝ)^6321
        have hw : |(658328233/1250000000 : ℝ)|=(658328233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348014701/2500000000 : ℝ)|^8369 ≤ (11035278424709/25000000000000 : ℝ)^6321
        have hw : |(1348014701/2500000000 : ℝ)|=(1348014701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312594393/10000000000 : ℝ)*x 0 + (-2088922049/10000000000 : ℝ)*x 1 + (5392057611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312594393/10000000000 : ℝ)^8369 ≤ (8656377484941/20000000000000 : ℝ)^6321 := by
    have hnat : (5312594393 : ℕ)^8369*20000000000000^6321 ≤ 8656377484941^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312594393 10000000000 8656377484941 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088922049/10000000000 : ℝ)^8369 ≤ (1257701179359/10000000000000 : ℝ)^6321 := by
    have hnat : (2088922049 : ℕ)^8369*10000000000000^6321 ≤ 1257701179359^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088922049 10000000000 1257701179359 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392057611/10000000000 : ℝ)^8369 ≤ (4414110076829/10000000000000 : ℝ)^6321 := by
    have hnat : (5392057611 : ℕ)^8369*10000000000000^6321 ≤ 4414110076829^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392057611 10000000000 4414110076829 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312594393/10000000000 : ℝ), (-2088922049/10000000000 : ℝ), (5392057611/10000000000 : ℝ)] ![(8656377484941/20000000000000 : ℝ), (1257701179359/10000000000000 : ℝ), (4414110076829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312594393/10000000000 : ℝ)|^8369 ≤ (8656377484941/20000000000000 : ℝ)^6321
        have hw : |(5312594393/10000000000 : ℝ)|=(5312594393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088922049/10000000000 : ℝ)|^8369 ≤ (1257701179359/10000000000000 : ℝ)^6321
        have hw : |(-2088922049/10000000000 : ℝ)|=(2088922049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392057611/10000000000 : ℝ)|^8369 ≤ (4414110076829/10000000000000 : ℝ)^6321
        have hw : |(5392057611/10000000000 : ℝ)|=(5392057611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062518747/2000000000 : ℝ)*x 0 + (1348014619/2500000000 : ℝ)*x 1 + (-2088921763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518747/2000000000 : ℝ)^8369 ≤ (43281880327077/100000000000000 : ℝ)^6321 := by
    have hnat : (1062518747 : ℕ)^8369*100000000000000^6321 ≤ 43281880327077^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518747 2000000000 43281880327077 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348014619/2500000000 : ℝ)^8369 ≤ (44141110143749/100000000000000 : ℝ)^6321 := by
    have hnat : (1348014619 : ℕ)^8369*100000000000000^6321 ≤ 44141110143749^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348014619 2500000000 44141110143749 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088921763/10000000000 : ℝ)^8369 ≤ (503080380549/4000000000000 : ℝ)^6321 := by
    have hnat : (2088921763 : ℕ)^8369*4000000000000^6321 ≤ 503080380549^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088921763 10000000000 503080380549 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062518747/2000000000 : ℝ), (1348014619/2500000000 : ℝ), (-2088921763/10000000000 : ℝ)] ![(43281880327077/100000000000000 : ℝ), (44141110143749/100000000000000 : ℝ), (503080380549/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062518747/2000000000 : ℝ)|^8369 ≤ (43281880327077/100000000000000 : ℝ)^6321
        have hw : |(1062518747/2000000000 : ℝ)|=(1062518747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348014619/2500000000 : ℝ)|^8369 ≤ (44141110143749/100000000000000 : ℝ)^6321
        have hw : |(1348014619/2500000000 : ℝ)|=(1348014619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088921763/10000000000 : ℝ)|^8369 ≤ (503080380549/4000000000000 : ℝ)^6321
        have hw : |(-2088921763/10000000000 : ℝ)|=(2088921763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s8_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174396679/400000000 : ℝ)*x 0 + (1121829123/2500000000 : ℝ)*x 1 + (105902711/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174396679/400000000 : ℝ)^8369 ≤ (33317268618633/100000000000000 : ℝ)^6321 := by
    have hnat : (174396679 : ℕ)^8369*100000000000000^6321 ≤ 33317268618633^6321*400000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174396679 400000000 33317268618633 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121829123/2500000000 : ℝ)^8369 ≤ (34612312257929/100000000000000 : ℝ)^6321 := by
    have hnat : (1121829123 : ℕ)^8369*100000000000000^6321 ≤ 34612312257929^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121829123 2500000000 34612312257929 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105902711/250000000 : ℝ)^8369 ≤ (32070419109489/100000000000000 : ℝ)^6321 := by
    have hnat : (105902711 : ℕ)^8369*100000000000000^6321 ≤ 32070419109489^6321*250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105902711 250000000 32070419109489 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174396679/400000000 : ℝ), (1121829123/2500000000 : ℝ), (105902711/250000000 : ℝ)] ![(33317268618633/100000000000000 : ℝ), (34612312257929/100000000000000 : ℝ), (32070419109489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174396679/400000000 : ℝ)|^8369 ≤ (33317268618633/100000000000000 : ℝ)^6321
        have hw : |(174396679/400000000 : ℝ)|=(174396679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121829123/2500000000 : ℝ)|^8369 ≤ (34612312257929/100000000000000 : ℝ)^6321
        have hw : |(1121829123/2500000000 : ℝ)|=(1121829123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105902711/250000000 : ℝ)|^8369 ≤ (32070419109489/100000000000000 : ℝ)^6321
        have hw : |(105902711/250000000 : ℝ)|=(105902711/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2849/25000 : ℝ) ^ (523/128 : ℝ) ≤ (6997121730023527/50000000000000000000 : ℝ) := by
    have hpowers : (2849/25000 : ℝ)^523 ≤ (6997121730023527/50000000000000000000 : ℝ)^128 := by
      have hnat : (2849 : ℕ)^523*50000000000000000000^128 ≤ 6997121730023527^128*25000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 25000 6997121730023527 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/25000 : ℝ)) (X := (6997121730023527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (523/128 : ℝ) ≤ (4137774347681821/12500000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^523 ≤ (4137774347681821/12500000000000000000 : ℝ)^128 := by
      have hnat : (14069 : ℕ)^523*12500000000000000000^128 ≤ 4137774347681821^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 4137774347681821 12500000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (4137774347681821/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006997121730023527/25000000000000000000 : ℝ) ≤ (10000684923086239/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25006997121730023527/25000000000000000000 : ℝ)^128 ≤ (10000684923086239/10000000000000000 : ℝ)^523 := by
      have hnat : (25006997121730023527 : ℕ)^128*10000000000000000^523 ≤ 10000684923086239^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006997121730023527 25000000000000000000 10000684923086239 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684923086239/10000000000000000 : ℝ)) (X := (25006997121730023527/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023548219120750811/50000000000000000000 : ℝ) ≤ (5000576221056427/5000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50023548219120750811/50000000000000000000 : ℝ)^128 ≤ (5000576221056427/5000000000000000 : ℝ)^523 := by
      have hnat : (50023548219120750811 : ℕ)^128*5000000000000000^523 ≤ 5000576221056427^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023548219120750811 50000000000000000000 5000576221056427 5000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000576221056427/5000000000000000 : ℝ)) (X := (50023548219120750811/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254137774347681821/6250000000000000000 : ℝ) ≤ (10001619961139469/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (6254137774347681821/6250000000000000000 : ℝ)^128 ≤ (10001619961139469/10000000000000000 : ℝ)^523 := by
      have hnat : (6254137774347681821 : ℕ)^128*10000000000000000^523 ≤ 10001619961139469^523*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254137774347681821 6250000000000000000 10001619961139469 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001619961139469/10000000000000000 : ℝ)) (X := (6254137774347681821/6250000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6997121730023527/50000000000000000000 : ℝ) ≤ ((2429197736886809797/2430000000000000000 : ℝ)+2*(93503805323/53460000000000 : ℝ)*(2849/25000 : ℝ))^(523/128 : ℝ) := by
    rw [show (2429197736886809797/2430000000000000000 : ℝ)+2*(93503805323/53460000000000 : ℝ)*(2849/25000 : ℝ)=(10000684923086239/10000000000000000 : ℝ) by norm_num, show 1+2*(6997121730023527/50000000000000000000 : ℝ)=(25006997121730023527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4137774347681821/12500000000000000000 : ℝ)+(6997121730023527/50000000000000000000 : ℝ) ≤ ((2429197736886809797/2430000000000000000 : ℝ)+(93503805323/53460000000000 : ℝ)*((14069/100000 : ℝ)+(2849/25000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (2429197736886809797/2430000000000000000 : ℝ)+(93503805323/53460000000000 : ℝ)*((14069/100000 : ℝ)+(2849/25000 : ℝ))=(5000576221056427/5000000000000000 : ℝ) by norm_num, show 1+(4137774347681821/12500000000000000000 : ℝ)+(6997121730023527/50000000000000000000 : ℝ)=(50023548219120750811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4137774347681821/12500000000000000000 : ℝ) ≤ ((2429197736886809797/2430000000000000000 : ℝ)+2*(93503805323/53460000000000 : ℝ)*(14069/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (2429197736886809797/2430000000000000000 : ℝ)+2*(93503805323/53460000000000 : ℝ)*(14069/100000 : ℝ)=(10001619961139469/10000000000000000 : ℝ) by norm_num, show 1+2*(4137774347681821/12500000000000000000 : ℝ)=(6254137774347681821/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2429197736886809797/2430000000000000000 : ℝ)*(X 1 0+X 2 0)+(93503805323/53460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (2429197736886809797/2430000000000000000 : ℝ)) (alpha := (93503805323/53460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2429197736886809797/2430000000000000000 : ℝ)*(X 0 1+X 2 1)+(93503805323/53460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (2429197736886809797/2430000000000000000 : ℝ)) (alpha := (93503805323/53460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2429197736886809797/2430000000000000000 : ℝ)*(X 0 2+X 1 2)+(93503805323/53460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (2429197736886809797/2430000000000000000 : ℝ)) (alpha := (93503805323/53460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-134421011/625000000 : ℝ)*X 0 0+(1078475241/2000000000 : ℝ)*X 0 1+(5266309433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344613041/10000000000 : ℝ)*X 1 0+(-2214670447/10000000000 : ℝ)*X 1 1+(5266309449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672306519/5000000000 : ℝ)*X 2 0+(1053261889/2000000000 : ℝ)*X 2 1+(-2214670457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359907147/10000000000 : ℝ)*X 0 0+(529433913/1250000000 : ℝ)*X 0 1+(70124243/156250000 : ℝ)*X 0 2+(4359907147/10000000000 : ℝ)*X 1 0+(529433913/1250000000 : ℝ)*X 1 1+(70124243/156250000 : ℝ)*X 1 2+(4359907147/10000000000 : ℝ)*X 2 0+(529433913/1250000000 : ℝ)*X 2 1+(70124243/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268842591/1250000000 : ℝ)*X 0 0+(658328233/1250000000 : ℝ)*X 0 1+(1348014701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312594393/10000000000 : ℝ)*X 1 0+(-2088922049/10000000000 : ℝ)*X 1 1+(5392057611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062518747/2000000000 : ℝ)*X 2 0+(1348014619/2500000000 : ℝ)*X 2 1+(-2088921763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174396679/400000000 : ℝ)*X 0 0+(1121829123/2500000000 : ℝ)*X 0 1+(105902711/250000000 : ℝ)*X 0 2+(174396679/400000000 : ℝ)*X 1 0+(1121829123/2500000000 : ℝ)*X 1 1+(105902711/250000000 : ℝ)*X 1 2+(174396679/400000000 : ℝ)*X 2 0+(1121829123/2500000000 : ℝ)*X 2 1+(105902711/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (818697599248004644556962553/74250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1084653657/50000000000000 : ℝ)*(base19) + (63261753/3125000000000 : ℝ)*(base23) + (37540201/50000000000000 : ℝ)*(lower2) + (143793369/50000000000000 : ℝ)*(upper3) + (167429079/100000000000000 : ℝ)*(upper5) + (5946597425071123/100000000000000 : ℝ)*(major0) + (5946597425071123/100000000000000 : ℝ)*(major1) + (5946597425071123/100000000000000 : ℝ)*(major2) + (7932367656289173/100000000000000 : ℝ)*(sp0) + (3966212643763747/50000000000000 : ℝ)*(sp1) + (991553179057339/12500000000000 : ℝ)*(sp2) + (3960734779210013/100000000000000 : ℝ)*(sp3) + (11960109127/20000000000000 : ℝ)*(sp4) + (80616391/250000000000 : ℝ)*(sp7) + (990191756441603/25000000000000 : ℝ)*(f.failure) + (7932427456834807/100000000000000 : ℝ)*(f.sum) + (712499851457/267300000000000000000000000 : ℝ)*base65 + (14281874592794537447/891000000000000000000000000000000 : ℝ)*base67 + (16272682431506537447/891000000000000000000000000000000 : ℝ)*base69 + (2224636004366537447/891000000000000000000000000000000 : ℝ)*base71 + (15477755306147/2673000000000000000000000000 : ℝ)*base73 + (20951945922419537447/891000000000000000000000000000000 : ℝ)*base75 + (18731802922784537447/891000000000000000000000000000000 : ℝ)*base77 + (767563344090462553/891000000000000000000000000000000 : ℝ)*base80 + (8267902188713/2673000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (19313837/2500000000000000000000 : ℝ)*base90 + (19313837/2500000000000000000000 : ℝ)*base92 + (19313837/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (380477377654726673373650759/49500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11322739/1000000000000 : ℝ)*(base19) + (902636977/100000000000000 : ℝ)*(base23) + (23668717/100000000000000 : ℝ)*(lower1) + (16717567/5000000000000 : ℝ)*(lower4) + (220820711/100000000000000 : ℝ)*(upper5) + (5976600697584531/100000000000000 : ℝ)*(major0) + (5976600697584531/100000000000000 : ℝ)*(major1) + (5976600697584531/100000000000000 : ℝ)*(major2) + (36026959029/100000000000000 : ℝ)*(sp0) + (20812349/97656250000 : ℝ)*(sp2) + (7972414225890667/100000000000000 : ℝ)*(sp4) + (1993112280143949/25000000000000 : ℝ)*(sp5) + (7972428038367343/100000000000000 : ℝ)*(sp6) + (1990375443052817/50000000000000 : ℝ)*(sp7) + (1990375443052817/50000000000000 : ℝ)*(f.failure) + (249139070401553/3125000000000 : ℝ)*(f.sum) + (269149323533/297000000000000000000000000 : ℝ)*base66 + (563778722277983249/99000000000000000000000000000000 : ℝ)*base68 + (1483768063053983249/99000000000000000000000000000000 : ℝ)*base70 + (873036587160983249/99000000000000000000000000000000 : ℝ)*base72 + (1371902954629/297000000000000000000000000 : ℝ)*base73 + (2974527935622983249/99000000000000000000000000000000 : ℝ)*base76 + (51227347095983249/99000000000000000000000000000000 : ℝ)*base78 + (1285014448422983249/99000000000000000000000000000000 : ℝ)*base80 + (724251819193/148500000000000000000000000 : ℝ)*base82 + (66446657/5000000000000000000000 : ℝ)*base89 + (66446657/5000000000000000000000 : ℝ)*base91 + (66446657/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1176_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1176_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1176_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1176_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1176_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
