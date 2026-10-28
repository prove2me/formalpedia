-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:11.997482+00:00
-- url     : https://prove2.me/submissions/e1b6b45f-1e91-4b92-abd8-b6a1a2202a63

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
theorem support_rectangle_w1118_s9_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089211227/5000000000 : ℝ)*x 0 + (5393407503/10000000000 : ℝ)*x 1 + (2632698347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089211227/5000000000 : ℝ)^8311 ≤ (13234717598297/100000000000000 : ℝ)^6263 := by
    have hnat : (1089211227 : ℕ)^8311*100000000000000^6263 ≤ 13234717598297^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089211227 5000000000 13234717598297 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393407503/10000000000 : ℝ)^8311 ≤ (22037004480597/50000000000000 : ℝ)^6263 := by
    have hnat : (5393407503 : ℕ)^8311*50000000000000^6263 ≤ 22037004480597^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393407503 10000000000 22037004480597 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632698347/5000000000 : ℝ)^8311 ≤ (21345636712079/50000000000000 : ℝ)^6263 := by
    have hnat : (2632698347 : ℕ)^8311*50000000000000^6263 ≤ 21345636712079^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632698347 5000000000 21345636712079 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089211227/5000000000 : ℝ), (5393407503/10000000000 : ℝ), (2632698347/5000000000 : ℝ)] ![(13234717598297/100000000000000 : ℝ), (22037004480597/50000000000000 : ℝ), (21345636712079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089211227/5000000000 : ℝ)|^8311 ≤ (13234717598297/100000000000000 : ℝ)^6263
        have hw : |(-1089211227/5000000000 : ℝ)|=(1089211227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393407503/10000000000 : ℝ)|^8311 ≤ (22037004480597/50000000000000 : ℝ)^6263
        have hw : |(5393407503/10000000000 : ℝ)|=(5393407503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632698347/5000000000 : ℝ)|^8311 ≤ (21345636712079/50000000000000 : ℝ)^6263
        have hw : |(2632698347/5000000000 : ℝ)|=(2632698347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s9_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068965257/2000000000 : ℝ)*x 0 + (-2243357017/10000000000 : ℝ)*x 1 + (526539673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068965257/2000000000 : ℝ)^8311 ≤ (21773985417749/50000000000000 : ℝ)^6263 := by
    have hnat : (1068965257 : ℕ)^8311*50000000000000^6263 ≤ 21773985417749^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068965257 2000000000 21773985417749 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243357017/10000000000 : ℝ)^8311 ≤ (3440188833069/25000000000000 : ℝ)^6263 := by
    have hnat : (2243357017 : ℕ)^8311*25000000000000^6263 ≤ 3440188833069^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243357017 10000000000 3440188833069 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526539673/1000000000 : ℝ)^8311 ≤ (1334102306609/3125000000000 : ℝ)^6263 := by
    have hnat : (526539673 : ℕ)^8311*3125000000000^6263 ≤ 1334102306609^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526539673 1000000000 1334102306609 3125000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068965257/2000000000 : ℝ), (-2243357017/10000000000 : ℝ), (526539673/1000000000 : ℝ)] ![(21773985417749/50000000000000 : ℝ), (3440188833069/25000000000000 : ℝ), (1334102306609/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068965257/2000000000 : ℝ)|^8311 ≤ (21773985417749/50000000000000 : ℝ)^6263
        have hw : |(1068965257/2000000000 : ℝ)|=(1068965257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2243357017/10000000000 : ℝ)|^8311 ≤ (3440188833069/25000000000000 : ℝ)^6263
        have hw : |(-2243357017/10000000000 : ℝ)|=(2243357017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526539673/1000000000 : ℝ)|^8311 ≤ (1334102306609/3125000000000 : ℝ)^6263
        have hw : |(526539673/1000000000 : ℝ)|=(526539673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s9_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672413127/5000000000 : ℝ)*x 0 + (1053079347/2000000000 : ℝ)*x 1 + (-560839263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672413127/5000000000 : ℝ)^8311 ≤ (43547970500327/100000000000000 : ℝ)^6263 := by
    have hnat : (2672413127 : ℕ)^8311*100000000000000^6263 ≤ 43547970500327^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672413127 5000000000 43547970500327 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053079347/2000000000 : ℝ)^8311 ≤ (10672818466321/25000000000000 : ℝ)^6263 := by
    have hnat : (1053079347 : ℕ)^8311*25000000000000^6263 ≤ 10672818466321^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053079347 2000000000 10672818466321 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560839263/2500000000 : ℝ)^8311 ≤ (13760755617169/100000000000000 : ℝ)^6263 := by
    have hnat : (560839263 : ℕ)^8311*100000000000000^6263 ≤ 13760755617169^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560839263 2500000000 13760755617169 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672413127/5000000000 : ℝ), (1053079347/2000000000 : ℝ), (-560839263/2500000000 : ℝ)] ![(43547970500327/100000000000000 : ℝ), (10672818466321/25000000000000 : ℝ), (13760755617169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672413127/5000000000 : ℝ)|^8311 ≤ (43547970500327/100000000000000 : ℝ)^6263
        have hw : |(2672413127/5000000000 : ℝ)|=(2672413127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053079347/2000000000 : ℝ)|^8311 ≤ (10672818466321/25000000000000 : ℝ)^6263
        have hw : |(1053079347/2000000000 : ℝ)|=(1053079347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560839263/2500000000 : ℝ)|^8311 ≤ (13760755617169/100000000000000 : ℝ)^6263
        have hw : |(-560839263/2500000000 : ℝ)|=(560839263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s9_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092016991/2500000000 : ℝ)*x 0 + (2121585019/5000000000 : ℝ)*x 1 + (4496645857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092016991/2500000000 : ℝ)^8311 ≤ (33316860779951/100000000000000 : ℝ)^6263 := by
    have hnat : (1092016991 : ℕ)^8311*100000000000000^6263 ≤ 33316860779951^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092016991 2500000000 33316860779951 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121585019/5000000000 : ℝ)^8311 ≤ (6411730554481/20000000000000 : ℝ)^6263 := by
    have hnat : (2121585019 : ℕ)^8311*20000000000000^6263 ≤ 6411730554481^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121585019 5000000000 6411730554481 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496645857/10000000000 : ℝ)^8311 ≤ (34624486442653/100000000000000 : ℝ)^6263 := by
    have hnat : (4496645857 : ℕ)^8311*100000000000000^6263 ≤ 34624486442653^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496645857 10000000000 34624486442653 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092016991/2500000000 : ℝ), (2121585019/5000000000 : ℝ), (4496645857/10000000000 : ℝ)] ![(33316860779951/100000000000000 : ℝ), (6411730554481/20000000000000 : ℝ), (34624486442653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092016991/2500000000 : ℝ)|^8311 ≤ (33316860779951/100000000000000 : ℝ)^6263
        have hw : |(1092016991/2500000000 : ℝ)|=(1092016991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121585019/5000000000 : ℝ)|^8311 ≤ (6411730554481/20000000000000 : ℝ)^6263
        have hw : |(2121585019/5000000000 : ℝ)|=(2121585019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496645857/10000000000 : ℝ)|^8311 ≤ (34624486442653/100000000000000 : ℝ)^6263
        have hw : |(4496645857/10000000000 : ℝ)|=(4496645857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s9_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544606901/2500000000 : ℝ)*x 0 + (5265718437/10000000000 : ℝ)*x 1 + (2696542221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544606901/2500000000 : ℝ)^8311 ≤ (529390364707/4000000000000 : ℝ)^6263 := by
    have hnat : (544606901 : ℕ)^8311*4000000000000^6263 ≤ 529390364707^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544606901 2500000000 529390364707 4000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265718437/10000000000 : ℝ)^8311 ≤ (10673683786821/25000000000000 : ℝ)^6263 := by
    have hnat : (5265718437 : ℕ)^8311*25000000000000^6263 ≤ 10673683786821^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265718437 10000000000 10673683786821 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696542221/5000000000 : ℝ)^8311 ≤ (11017626429129/25000000000000 : ℝ)^6263 := by
    have hnat : (2696542221 : ℕ)^8311*25000000000000^6263 ≤ 11017626429129^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696542221 5000000000 11017626429129 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544606901/2500000000 : ℝ), (5265718437/10000000000 : ℝ), (2696542221/5000000000 : ℝ)] ![(529390364707/4000000000000 : ℝ), (10673683786821/25000000000000 : ℝ), (11017626429129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544606901/2500000000 : ℝ)|^8311 ≤ (529390364707/4000000000000 : ℝ)^6263
        have hw : |(-544606901/2500000000 : ℝ)|=(544606901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265718437/10000000000 : ℝ)|^8311 ≤ (10673683786821/25000000000000 : ℝ)^6263
        have hw : |(5265718437/10000000000 : ℝ)|=(5265718437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696542221/5000000000 : ℝ)|^8311 ≤ (11017626429129/25000000000000 : ℝ)^6263
        have hw : |(2696542221/5000000000 : ℝ)|=(2696542221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s9_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136502413/312500000 : ℝ)*x 0 + (2248005191/5000000000 : ℝ)*x 1 + (4243808313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136502413/312500000 : ℝ)^8311 ≤ (4164619303031/12500000000000 : ℝ)^6263 := by
    have hnat : (136502413 : ℕ)^8311*12500000000000^6263 ≤ 4164619303031^6263*312500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136502413 312500000 4164619303031 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248005191/5000000000 : ℝ)^8311 ≤ (34617993314709/100000000000000 : ℝ)^6263 := by
    have hnat : (2248005191 : ℕ)^8311*100000000000000^6263 ≤ 34617993314709^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248005191 5000000000 34617993314709 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243808313/10000000000 : ℝ)^8311 ≤ (32065052245499/100000000000000 : ℝ)^6263 := by
    have hnat : (4243808313 : ℕ)^8311*100000000000000^6263 ≤ 32065052245499^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243808313 10000000000 32065052245499 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136502413/312500000 : ℝ), (2248005191/5000000000 : ℝ), (4243808313/10000000000 : ℝ)] ![(4164619303031/12500000000000 : ℝ), (34617993314709/100000000000000 : ℝ), (32065052245499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136502413/312500000 : ℝ)|^8311 ≤ (4164619303031/12500000000000 : ℝ)^6263
        have hw : |(136502413/312500000 : ℝ)|=(136502413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248005191/5000000000 : ℝ)|^8311 ≤ (34617993314709/100000000000000 : ℝ)^6263
        have hw : |(2248005191/5000000000 : ℝ)|=(2248005191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243808313/10000000000 : ℝ)|^8311 ≤ (32065052245499/100000000000000 : ℝ)^6263
        have hw : |(4243808313/10000000000 : ℝ)|=(4243808313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/50000 : ℝ) ^ (4155/1024 : ℝ) ≤ (3623450423652951/25000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^4155 ≤ (3623450423652951/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5661 : ℕ)^4155*25000000000000000000^1024 ≤ 3623450423652951^1024*50000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 3623450423652951 25000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (3623450423652951/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (4155/1024 : ℝ) ≤ (34640877420498181/100000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^4155 ≤ (34640877420498181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7017 : ℕ)^4155*100000000000000000000^1024 ≤ 34640877420498181^1024*50000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 34640877420498181 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (34640877420498181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503623450423652951/12500000000000000000 : ℝ) ≤ (10000714321647833/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (12503623450423652951/12500000000000000000 : ℝ)^1024 ≤ (10000714321647833/10000000000000000 : ℝ)^4155 := by
      have hnat : (12503623450423652951 : ℕ)^1024*10000000000000000^4155 ≤ 10000714321647833^4155*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503623450423652951 12500000000000000000 10000714321647833 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714321647833/10000000000000000 : ℝ)) (X := (12503623450423652951/12500000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009826935823021997/20000000000000000000 : ℝ) ≤ (1250151337543971/1250000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (20009826935823021997/20000000000000000000 : ℝ)^1024 ≤ (1250151337543971/1250000000000000 : ℝ)^4155 := by
      have hnat : (20009826935823021997 : ℕ)^1024*1250000000000000^4155 ≤ 1250151337543971^4155*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009826935823021997 20000000000000000000 1250151337543971 1250000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151337543971/1250000000000000 : ℝ)) (X := (20009826935823021997/20000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034640877420498181/50000000000000000000 : ℝ) ≤ (10001707079055703/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50034640877420498181/50000000000000000000 : ℝ)^1024 ≤ (10001707079055703/10000000000000000 : ℝ)^4155 := by
      have hnat : (50034640877420498181 : ℕ)^1024*10000000000000000^4155 ≤ 10001707079055703^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034640877420498181 50000000000000000000 10001707079055703 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001707079055703/10000000000000000 : ℝ)) (X := (50034640877420498181/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3623450423652951/25000000000000000000 : ℝ) ≤ ((2259224770078084913/2260000000000000000 : ℝ)+2*(99275740787/54240000000000 : ℝ)*(5661/50000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (2259224770078084913/2260000000000000000 : ℝ)+2*(99275740787/54240000000000 : ℝ)*(5661/50000 : ℝ)=(10000714321647833/10000000000000000 : ℝ) by norm_num, show 1+2*(3623450423652951/25000000000000000000 : ℝ)=(12503623450423652951/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34640877420498181/100000000000000000000 : ℝ)+(3623450423652951/25000000000000000000 : ℝ) ≤ ((2259224770078084913/2260000000000000000 : ℝ)+(99275740787/54240000000000 : ℝ)*((7017/50000 : ℝ)+(5661/50000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (2259224770078084913/2260000000000000000 : ℝ)+(99275740787/54240000000000 : ℝ)*((7017/50000 : ℝ)+(5661/50000 : ℝ))=(1250151337543971/1250000000000000 : ℝ) by norm_num, show 1+(34640877420498181/100000000000000000000 : ℝ)+(3623450423652951/25000000000000000000 : ℝ)=(20009826935823021997/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34640877420498181/100000000000000000000 : ℝ) ≤ ((2259224770078084913/2260000000000000000 : ℝ)+2*(99275740787/54240000000000 : ℝ)*(7017/50000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (2259224770078084913/2260000000000000000 : ℝ)+2*(99275740787/54240000000000 : ℝ)*(7017/50000 : ℝ)=(10001707079055703/10000000000000000 : ℝ) by norm_num, show 1+2*(34640877420498181/100000000000000000000 : ℝ)=(50034640877420498181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2259224770078084913/2260000000000000000 : ℝ)*(X 1 0+X 2 0)+(99275740787/54240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2259224770078084913/2260000000000000000 : ℝ)) (alpha := (99275740787/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2259224770078084913/2260000000000000000 : ℝ)*(X 0 1+X 2 1)+(99275740787/54240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2259224770078084913/2260000000000000000 : ℝ)) (alpha := (99275740787/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2259224770078084913/2260000000000000000 : ℝ)*(X 0 2+X 1 2)+(99275740787/54240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2259224770078084913/2260000000000000000 : ℝ)) (alpha := (99275740787/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089211227/5000000000 : ℝ)*X 0 0+(5393407503/10000000000 : ℝ)*X 0 1+(2632698347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068965257/2000000000 : ℝ)*X 1 0+(-2243357017/10000000000 : ℝ)*X 1 1+(526539673/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672413127/5000000000 : ℝ)*X 2 0+(1053079347/2000000000 : ℝ)*X 2 1+(-560839263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092016991/2500000000 : ℝ)*X 0 0+(2121585019/5000000000 : ℝ)*X 0 1+(4496645857/10000000000 : ℝ)*X 0 2+(1092016991/2500000000 : ℝ)*X 1 0+(2121585019/5000000000 : ℝ)*X 1 1+(4496645857/10000000000 : ℝ)*X 1 2+(1092016991/2500000000 : ℝ)*X 2 0+(2121585019/5000000000 : ℝ)*X 2 1+(4496645857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-544606901/2500000000 : ℝ)*X 0 0+(5265718437/10000000000 : ℝ)*X 0 1+(2696542221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((136502413/312500000 : ℝ)*X 0 0+(2248005191/5000000000 : ℝ)*X 0 1+(4243808313/10000000000 : ℝ)*X 0 2+(136502413/312500000 : ℝ)*X 1 0+(2248005191/5000000000 : ℝ)*X 1 1+(4243808313/10000000000 : ℝ)*X 1 2+(136502413/312500000 : ℝ)*X 2 0+(2248005191/5000000000 : ℝ)*X 2 1+(4243808313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240184041505050279130489983/113000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86551157/20000000000000 : ℝ)*(base19) + (76474559/20000000000000 : ℝ)*(base23) + (2712043/100000000000000 : ℝ)*(lower2) + (76661533/100000000000000 : ℝ)*(upper3) + (1107597/12500000000000 : ℝ)*(upper5) + (5878515687622599/100000000000000 : ℝ)*(major0) + (5878515687622599/100000000000000 : ℝ)*(major1) + (5878515687622599/100000000000000 : ℝ)*(major2) + (7811856248190539/100000000000000 : ℝ)*(sp0) + (3905934030226833/50000000000000 : ℝ)*(sp1) + (488241756927291/6250000000000 : ℝ)*(sp2) + (986288890269591/25000000000000 : ℝ)*(sp3) + (12245018913/100000000000000 : ℝ)*(sp4) + (7250106621/100000000000000 : ℝ)*(sp5) + (493145351398123/12500000000000 : ℝ)*(f.failure) + (7811868493209451/100000000000000 : ℝ)*(f.sum) + (47804681613/7232000000000000000000000 : ℝ)*base66 + (3285095149973376113/226000000000000000000000000000000 : ℝ)*base68 + (1986769848479376113/226000000000000000000000000000000 : ℝ)*base70 + (5251290333913376113/226000000000000000000000000000000 : ℝ)*base72 + (2956028001257/904000000000000000000000000 : ℝ)*base74 + (1092755108847376113/226000000000000000000000000000000 : ℝ)*base76 + (2501538347877376113/226000000000000000000000000000000 : ℝ)*base78 + (3693410493985376113/226000000000000000000000000000000 : ℝ)*base80 + (1408070392093/180800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (822887/250000000000000000000 : ℝ)*base90 + (822887/250000000000000000000 : ℝ)*base92 + (822887/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1118_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1118_box_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-256341953/1250000000 : ℝ)*x 0 + (2688323421/5000000000 : ℝ)*x 1 + (537664683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256341953/1250000000 : ℝ)^8311 ≤ (12215303154651/100000000000000 : ℝ)^6263 := by
    have hnat : (256341953 : ℕ)^8311*100000000000000^6263 ≤ 12215303154651^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256341953 1250000000 12215303154651 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688323421/5000000000 : ℝ)^8311 ≤ (21946174240029/50000000000000 : ℝ)^6263 := by
    have hnat : (2688323421 : ℕ)^8311*50000000000000^6263 ≤ 21946174240029^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688323421 5000000000 21946174240029 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537664683/1000000000 : ℝ)^8311 ≤ (43892348350063/100000000000000 : ℝ)^6263 := by
    have hnat : (537664683 : ℕ)^8311*100000000000000^6263 ≤ 43892348350063^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537664683 1000000000 43892348350063 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256341953/1250000000 : ℝ), (2688323421/5000000000 : ℝ), (537664683/1000000000 : ℝ)] ![(12215303154651/100000000000000 : ℝ), (21946174240029/50000000000000 : ℝ), (43892348350063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256341953/1250000000 : ℝ)|^8311 ≤ (12215303154651/100000000000000 : ℝ)^6263
        have hw : |(-256341953/1250000000 : ℝ)|=(256341953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688323421/5000000000 : ℝ)|^8311 ≤ (21946174240029/50000000000000 : ℝ)^6263
        have hw : |(2688323421/5000000000 : ℝ)|=(2688323421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537664683/1000000000 : ℝ)|^8311 ≤ (43892348350063/100000000000000 : ℝ)^6263
        have hw : |(537664683/1000000000 : ℝ)|=(537664683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059151373/2000000000 : ℝ)*x 0 + (-432075149/2000000000 : ℝ)*x 1 + (2688323327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059151373/2000000000 : ℝ)^8311 ≤ (43018231298969/100000000000000 : ℝ)^6263 := by
    have hnat : (1059151373 : ℕ)^8311*100000000000000^6263 ≤ 43018231298969^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059151373 2000000000 43018231298969 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432075149/2000000000 : ℝ)^8311 ≤ (2617884449461/20000000000000 : ℝ)^6263 := by
    have hnat : (432075149 : ℕ)^8311*20000000000000^6263 ≤ 2617884449461^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432075149 2000000000 2617884449461 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688323327/5000000000 : ℝ)^8311 ≤ (43892346443457/100000000000000 : ℝ)^6263 := by
    have hnat : (2688323327 : ℕ)^8311*100000000000000^6263 ≤ 43892346443457^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688323327 5000000000 43892346443457 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059151373/2000000000 : ℝ), (-432075149/2000000000 : ℝ), (2688323327/5000000000 : ℝ)] ![(43018231298969/100000000000000 : ℝ), (2617884449461/20000000000000 : ℝ), (43892346443457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059151373/2000000000 : ℝ)|^8311 ≤ (43018231298969/100000000000000 : ℝ)^6263
        have hw : |(1059151373/2000000000 : ℝ)|=(1059151373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-432075149/2000000000 : ℝ)|^8311 ≤ (2617884449461/20000000000000 : ℝ)^6263
        have hw : |(-432075149/2000000000 : ℝ)|=(432075149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688323327/5000000000 : ℝ)|^8311 ≤ (43892346443457/100000000000000 : ℝ)^6263
        have hw : |(2688323327/5000000000 : ℝ)|=(2688323327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323939179/2500000000 : ℝ)*x 0 + (5376646729/10000000000 : ℝ)*x 1 + (-2160375843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323939179/2500000000 : ℝ)^8311 ≤ (8603645938567/20000000000000 : ℝ)^6263 := by
    have hnat : (1323939179 : ℕ)^8311*20000000000000^6263 ≤ 8603645938567^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323939179 2500000000 8603645938567 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376646729/10000000000 : ℝ)^8311 ≤ (43892347255931/100000000000000 : ℝ)^6263 := by
    have hnat : (5376646729 : ℕ)^8311*100000000000000^6263 ≤ 43892347255931^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376646729 10000000000 43892347255931 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160375843/10000000000 : ℝ)^8311 ≤ (3272355758809/25000000000000 : ℝ)^6263 := by
    have hnat : (2160375843 : ℕ)^8311*25000000000000^6263 ≤ 3272355758809^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160375843 10000000000 3272355758809 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323939179/2500000000 : ℝ), (5376646729/10000000000 : ℝ), (-2160375843/10000000000 : ℝ)] ![(8603645938567/20000000000000 : ℝ), (43892347255931/100000000000000 : ℝ), (3272355758809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323939179/2500000000 : ℝ)|^8311 ≤ (8603645938567/20000000000000 : ℝ)^6263
        have hw : |(1323939179/2500000000 : ℝ)|=(1323939179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376646729/10000000000 : ℝ)|^8311 ≤ (43892347255931/100000000000000 : ℝ)^6263
        have hw : |(5376646729/10000000000 : ℝ)|=(5376646729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2160375843/10000000000 : ℝ)|^8311 ≤ (3272355758809/25000000000000 : ℝ)^6263
        have hw : |(-2160375843/10000000000 : ℝ)|=(2160375843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1118966157/2500000000 : ℝ)*x 0 + (4316293903/10000000000 : ℝ)*x 1 + (172651761/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118966157/2500000000 : ℝ)^8311 ≤ (17206152321179/50000000000000 : ℝ)^6263 := by
    have hnat : (1118966157 : ℕ)^8311*50000000000000^6263 ≤ 17206152321179^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118966157 2500000000 17206152321179 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316293903/10000000000 : ℝ)^8311 ≤ (3279384705971/10000000000000 : ℝ)^6263 := by
    have hnat : (4316293903 : ℕ)^8311*10000000000000^6263 ≤ 3279384705971^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316293903 10000000000 3279384705971 10000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172651761/400000000 : ℝ)^8311 ≤ (3279384828973/10000000000000 : ℝ)^6263 := by
    have hnat : (172651761 : ℕ)^8311*10000000000000^6263 ≤ 3279384828973^6263*400000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172651761 400000000 3279384828973 10000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118966157/2500000000 : ℝ), (4316293903/10000000000 : ℝ), (172651761/400000000 : ℝ)] ![(17206152321179/50000000000000 : ℝ), (3279384705971/10000000000000 : ℝ), (3279384828973/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118966157/2500000000 : ℝ)|^8311 ≤ (17206152321179/50000000000000 : ℝ)^6263
        have hw : |(1118966157/2500000000 : ℝ)|=(1118966157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316293903/10000000000 : ℝ)|^8311 ≤ (3279384705971/10000000000000 : ℝ)^6263
        have hw : |(4316293903/10000000000 : ℝ)|=(4316293903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172651761/400000000 : ℝ)|^8311 ≤ (3279384828973/10000000000000 : ℝ)^6263
        have hw : |(172651761/400000000 : ℝ)|=(172651761/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-18027243/78125000 : ℝ)*x 0 + (2640415143/5000000000 : ℝ)*x 1 + (2640415223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18027243/78125000 : ℝ)^8311 ≤ (1785648373891/12500000000000 : ℝ)^6263 := by
    have hnat : (18027243 : ℕ)^8311*12500000000000^6263 ≤ 1785648373891^6263*78125000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18027243 78125000 1785648373891 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640415143/5000000000 : ℝ)^8311 ≤ (42857405634679/100000000000000 : ℝ)^6263 := by
    have hnat : (2640415143 : ℕ)^8311*100000000000000^6263 ≤ 42857405634679^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640415143 5000000000 42857405634679 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640415223/5000000000 : ℝ)^8311 ≤ (8571481471559/20000000000000 : ℝ)^6263 := by
    have hnat : (2640415223 : ℕ)^8311*20000000000000^6263 ≤ 8571481471559^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640415223 5000000000 8571481471559 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18027243/78125000 : ℝ), (2640415143/5000000000 : ℝ), (2640415223/5000000000 : ℝ)] ![(1785648373891/12500000000000 : ℝ), (42857405634679/100000000000000 : ℝ), (8571481471559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18027243/78125000 : ℝ)|^8311 ≤ (1785648373891/12500000000000 : ℝ)^6263
        have hw : |(-18027243/78125000 : ℝ)|=(18027243/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640415143/5000000000 : ℝ)|^8311 ≤ (42857405634679/100000000000000 : ℝ)^6263
        have hw : |(2640415143/5000000000 : ℝ)|=(2640415143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640415223/5000000000 : ℝ)|^8311 ≤ (8571481471559/20000000000000 : ℝ)^6263
        have hw : |(2640415223/5000000000 : ℝ)|=(2640415223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363487877/10000000000 : ℝ)*x 0 + (-2197994539/10000000000 : ℝ)*x 1 + (5280830321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363487877/10000000000 : ℝ)^8311 ≤ (87499709343/200000000000 : ℝ)^6263 := by
    have hnat : (5363487877 : ℕ)^8311*200000000000^6263 ≤ 87499709343^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363487877 10000000000 87499709343 200000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197994539/10000000000 : ℝ)^8311 ≤ (13392739307703/100000000000000 : ℝ)^6263 := by
    have hnat : (2197994539 : ℕ)^8311*100000000000000^6263 ≤ 13392739307703^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197994539 10000000000 13392739307703 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280830321/10000000000 : ℝ)^8311 ≤ (42857406011611/100000000000000 : ℝ)^6263 := by
    have hnat : (5280830321 : ℕ)^8311*100000000000000^6263 ≤ 42857406011611^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280830321 10000000000 42857406011611 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363487877/10000000000 : ℝ), (-2197994539/10000000000 : ℝ), (5280830321/10000000000 : ℝ)] ![(87499709343/200000000000 : ℝ), (13392739307703/100000000000000 : ℝ), (42857406011611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363487877/10000000000 : ℝ)|^8311 ≤ (87499709343/200000000000 : ℝ)^6263
        have hw : |(5363487877/10000000000 : ℝ)|=(5363487877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197994539/10000000000 : ℝ)|^8311 ≤ (13392739307703/100000000000000 : ℝ)^6263
        have hw : |(-2197994539/10000000000 : ℝ)|=(2197994539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280830321/10000000000 : ℝ)|^8311 ≤ (42857406011611/100000000000000 : ℝ)^6263
        have hw : |(5280830321/10000000000 : ℝ)|=(5280830321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536348743/1000000000 : ℝ)*x 0 + (1320207539/2500000000 : ℝ)*x 1 + (-2197995357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536348743/1000000000 : ℝ)^8311 ≤ (21874924916517/50000000000000 : ℝ)^6263 := by
    have hnat : (536348743 : ℕ)^8311*50000000000000^6263 ≤ 21874924916517^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536348743 1000000000 21874924916517 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320207539/2500000000 : ℝ)^8311 ≤ (5357175529331/12500000000000 : ℝ)^6263 := by
    have hnat : (1320207539 : ℕ)^8311*12500000000000^6263 ≤ 5357175529331^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320207539 2500000000 5357175529331 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197995357/10000000000 : ℝ)^8311 ≤ (6696372960873/50000000000000 : ℝ)^6263 := by
    have hnat : (2197995357 : ℕ)^8311*50000000000000^6263 ≤ 6696372960873^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197995357 10000000000 6696372960873 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536348743/1000000000 : ℝ), (1320207539/2500000000 : ℝ), (-2197995357/10000000000 : ℝ)] ![(21874924916517/50000000000000 : ℝ), (5357175529331/12500000000000 : ℝ), (6696372960873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536348743/1000000000 : ℝ)|^8311 ≤ (21874924916517/50000000000000 : ℝ)^6263
        have hw : |(536348743/1000000000 : ℝ)|=(536348743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320207539/2500000000 : ℝ)|^8311 ≤ (5357175529331/12500000000000 : ℝ)^6263
        have hw : |(1320207539/2500000000 : ℝ)|=(1320207539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197995357/10000000000 : ℝ)|^8311 ≤ (6696372960873/50000000000000 : ℝ)^6263
        have hw : |(-2197995357/10000000000 : ℝ)|=(2197995357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4259919987/10000000000 : ℝ)*x 0 + (2212122463/5000000000 : ℝ)*x 1 + (4424245591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259919987/10000000000 : ℝ)^8311 ≤ (3222669528041/10000000000000 : ℝ)^6263 := by
    have hnat : (4259919987 : ℕ)^8311*10000000000000^6263 ≤ 3222669528041^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259919987 10000000000 3222669528041 10000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212122463/5000000000 : ℝ)^8311 ≤ (33886648969529/100000000000000 : ℝ)^6263 := by
    have hnat : (2212122463 : ℕ)^8311*100000000000000^6263 ≤ 33886648969529^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212122463 5000000000 33886648969529 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424245591/10000000000 : ℝ)^8311 ≤ (16943327864261/50000000000000 : ℝ)^6263 := by
    have hnat : (4424245591 : ℕ)^8311*50000000000000^6263 ≤ 16943327864261^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424245591 10000000000 16943327864261 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259919987/10000000000 : ℝ), (2212122463/5000000000 : ℝ), (4424245591/10000000000 : ℝ)] ![(3222669528041/10000000000000 : ℝ), (33886648969529/100000000000000 : ℝ), (16943327864261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259919987/10000000000 : ℝ)|^8311 ≤ (3222669528041/10000000000000 : ℝ)^6263
        have hw : |(4259919987/10000000000 : ℝ)|=(4259919987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2212122463/5000000000 : ℝ)|^8311 ≤ (33886648969529/100000000000000 : ℝ)^6263
        have hw : |(2212122463/5000000000 : ℝ)|=(2212122463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424245591/10000000000 : ℝ)|^8311 ≤ (16943327864261/50000000000000 : ℝ)^6263
        have hw : |(4424245591/10000000000 : ℝ)|=(4424245591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_8 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2253824601/10000000000 : ℝ)*x 0 + (5215711999/10000000000 : ℝ)*x 1 + (5386252959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253824601/10000000000 : ℝ)^8311 ≤ (13846024505779/100000000000000 : ℝ)^6263 := by
    have hnat : (2253824601 : ℕ)^8311*100000000000000^6263 ≤ 13846024505779^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253824601 10000000000 13846024505779 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215711999/10000000000 : ℝ)^8311 ≤ (5269691710549/12500000000000 : ℝ)^6263 := by
    have hnat : (5215711999 : ℕ)^8311*12500000000000^6263 ≤ 5269691710549^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215711999 10000000000 5269691710549 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386252959/10000000000 : ℝ)^8311 ≤ (21998220898119/50000000000000 : ℝ)^6263 := by
    have hnat : (5386252959 : ℕ)^8311*50000000000000^6263 ≤ 21998220898119^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386252959 10000000000 21998220898119 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2253824601/10000000000 : ℝ), (5215711999/10000000000 : ℝ), (5386252959/10000000000 : ℝ)] ![(13846024505779/100000000000000 : ℝ), (5269691710549/12500000000000 : ℝ), (21998220898119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2253824601/10000000000 : ℝ)|^8311 ≤ (13846024505779/100000000000000 : ℝ)^6263
        have hw : |(-2253824601/10000000000 : ℝ)|=(2253824601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215711999/10000000000 : ℝ)|^8311 ≤ (5269691710549/12500000000000 : ℝ)^6263
        have hw : |(5215711999/10000000000 : ℝ)|=(5215711999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386252959/10000000000 : ℝ)|^8311 ≤ (21998220898119/50000000000000 : ℝ)^6263
        have hw : |(5386252959/10000000000 : ℝ)|=(5386252959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_9 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644481539/5000000000 : ℝ)*x 0 + (-539133549/2500000000 : ℝ)*x 1 + (2693126473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644481539/5000000000 : ℝ)^8311 ≤ (8589002716469/20000000000000 : ℝ)^6263 := by
    have hnat : (2644481539 : ℕ)^8311*20000000000000^6263 ≤ 8589002716469^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644481539 5000000000 8589002716469 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539133549/2500000000 : ℝ)^8311 ≤ (13058544749459/100000000000000 : ℝ)^6263 := by
    have hnat : (539133549 : ℕ)^8311*100000000000000^6263 ≤ 13058544749459^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539133549 2500000000 13058544749459 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693126473/5000000000 : ℝ)^8311 ≤ (43996441655327/100000000000000 : ℝ)^6263 := by
    have hnat : (2693126473 : ℕ)^8311*100000000000000^6263 ≤ 43996441655327^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693126473 5000000000 43996441655327 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644481539/5000000000 : ℝ), (-539133549/2500000000 : ℝ), (2693126473/5000000000 : ℝ)] ![(8589002716469/20000000000000 : ℝ), (13058544749459/100000000000000 : ℝ), (43996441655327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644481539/5000000000 : ℝ)|^8311 ≤ (8589002716469/20000000000000 : ℝ)^6263
        have hw : |(2644481539/5000000000 : ℝ)|=(2644481539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539133549/2500000000 : ℝ)|^8311 ≤ (13058544749459/100000000000000 : ℝ)^6263
        have hw : |(-539133549/2500000000 : ℝ)|=(539133549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693126473/5000000000 : ℝ)|^8311 ≤ (43996441655327/100000000000000 : ℝ)^6263
        have hw : |(2693126473/5000000000 : ℝ)|=(2693126473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_10 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288962929/10000000000 : ℝ)*x 0 + (5386252409/10000000000 : ℝ)*x 1 + (-26956689/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288962929/10000000000 : ℝ)^8311 ≤ (8589002395377/20000000000000 : ℝ)^6263 := by
    have hnat : (5288962929 : ℕ)^8311*20000000000000^6263 ≤ 8589002395377^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288962929 10000000000 8589002395377 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386252409/10000000000 : ℝ)^8311 ≤ (43996435834617/100000000000000 : ℝ)^6263 := by
    have hnat : (5386252409 : ℕ)^8311*100000000000000^6263 ≤ 43996435834617^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386252409 10000000000 43996435834617 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26956689/125000000 : ℝ)^8311 ≤ (65292760871/500000000000 : ℝ)^6263 := by
    have hnat : (26956689 : ℕ)^8311*500000000000^6263 ≤ 65292760871^6263*125000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26956689 125000000 65292760871 500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288962929/10000000000 : ℝ), (5386252409/10000000000 : ℝ), (-26956689/125000000 : ℝ)] ![(8589002395377/20000000000000 : ℝ), (43996435834617/100000000000000 : ℝ), (65292760871/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288962929/10000000000 : ℝ)|^8311 ≤ (8589002395377/20000000000000 : ℝ)^6263
        have hw : |(5288962929/10000000000 : ℝ)|=(5288962929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386252409/10000000000 : ℝ)|^8311 ≤ (43996435834617/100000000000000 : ℝ)^6263
        have hw : |(5386252409/10000000000 : ℝ)|=(5386252409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26956689/125000000 : ℝ)|^8311 ≤ (65292760871/500000000000 : ℝ)^6263
        have hw : |(-26956689/125000000 : ℝ)|=(26956689/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_11 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4497240891/10000000000 : ℝ)*x 0 + (21527327/50000000 : ℝ)*x 1 + (1076366309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497240891/10000000000 : ℝ)^8311 ≤ (6926113325279/20000000000000 : ℝ)^6263 := by
    have hnat : (4497240891 : ℕ)^8311*20000000000000^6263 ≤ 6926113325279^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497240891 10000000000 6926113325279 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21527327/50000000 : ℝ)^8311 ≤ (16342358753661/50000000000000 : ℝ)^6263 := by
    have hnat : (21527327 : ℕ)^8311*50000000000000^6263 ≤ 16342358753661^6263*50000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21527327 50000000 16342358753661 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076366309/2500000000 : ℝ)^8311 ≤ (32684715855211/100000000000000 : ℝ)^6263 := by
    have hnat : (1076366309 : ℕ)^8311*100000000000000^6263 ≤ 32684715855211^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076366309 2500000000 32684715855211 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497240891/10000000000 : ℝ), (21527327/50000000 : ℝ), (1076366309/2500000000 : ℝ)] ![(6926113325279/20000000000000 : ℝ), (16342358753661/50000000000000 : ℝ), (32684715855211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497240891/10000000000 : ℝ)|^8311 ≤ (6926113325279/20000000000000 : ℝ)^6263
        have hw : |(4497240891/10000000000 : ℝ)|=(4497240891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21527327/50000000 : ℝ)|^8311 ≤ (16342358753661/50000000000000 : ℝ)^6263
        have hw : |(21527327/50000000 : ℝ)|=(21527327/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076366309/2500000000 : ℝ)|^8311 ≤ (32684715855211/100000000000000 : ℝ)^6263
        have hw : |(1076366309/2500000000 : ℝ)|=(1076366309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_12 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-420946557/2000000000 : ℝ)*x 0 + (340029351/625000000 : ℝ)*x 1 + (527280327/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420946557/2000000000 : ℝ)^8311 ≤ (12643941621527/100000000000000 : ℝ)^6263 := by
    have hnat : (420946557 : ℕ)^8311*100000000000000^6263 ≤ 12643941621527^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420946557 2000000000 12643941621527 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340029351/625000000 : ℝ)^8311 ≤ (8917015598031/20000000000000 : ℝ)^6263 := by
    have hnat : (340029351 : ℕ)^8311*20000000000000^6263 ≤ 8917015598031^6263*625000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340029351 625000000 8917015598031 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527280327/1000000000 : ℝ)^8311 ≤ (10692745094243/25000000000000 : ℝ)^6263 := by
    have hnat : (527280327 : ℕ)^8311*25000000000000^6263 ≤ 10692745094243^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527280327 1000000000 10692745094243 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420946557/2000000000 : ℝ), (340029351/625000000 : ℝ), (527280327/1000000000 : ℝ)] ![(12643941621527/100000000000000 : ℝ), (8917015598031/20000000000000 : ℝ), (10692745094243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420946557/2000000000 : ℝ)|^8311 ≤ (12643941621527/100000000000000 : ℝ)^6263
        have hw : |(-420946557/2000000000 : ℝ)|=(420946557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340029351/625000000 : ℝ)|^8311 ≤ (8917015598031/20000000000000 : ℝ)^6263
        have hw : |(340029351/625000000 : ℝ)|=(340029351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527280327/1000000000 : ℝ)|^8311 ≤ (10692745094243/25000000000000 : ℝ)^6263
        have hw : |(527280327/1000000000 : ℝ)|=(527280327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_13 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369159351/10000000000 : ℝ)*x 0 + (-1100544379/5000000000 : ℝ)*x 1 + (2636401671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369159351/10000000000 : ℝ)^8311 ≤ (5476406883713/12500000000000 : ℝ)^6263 := by
    have hnat : (5369159351 : ℕ)^8311*12500000000000^6263 ≤ 5476406883713^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369159351 10000000000 5476406883713 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100544379/5000000000 : ℝ)^8311 ≤ (6708881881769/50000000000000 : ℝ)^6263 := by
    have hnat : (1100544379 : ℕ)^8311*50000000000000^6263 ≤ 6708881881769^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100544379 5000000000 6708881881769 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636401671/5000000000 : ℝ)^8311 ≤ (42770981151989/100000000000000 : ℝ)^6263 := by
    have hnat : (2636401671 : ℕ)^8311*100000000000000^6263 ≤ 42770981151989^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636401671 5000000000 42770981151989 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369159351/10000000000 : ℝ), (-1100544379/5000000000 : ℝ), (2636401671/5000000000 : ℝ)] ![(5476406883713/12500000000000 : ℝ), (6708881881769/50000000000000 : ℝ), (42770981151989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369159351/10000000000 : ℝ)|^8311 ≤ (5476406883713/12500000000000 : ℝ)^6263
        have hw : |(5369159351/10000000000 : ℝ)|=(5369159351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100544379/5000000000 : ℝ)|^8311 ≤ (6708881881769/50000000000000 : ℝ)^6263
        have hw : |(-1100544379/5000000000 : ℝ)|=(1100544379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636401671/5000000000 : ℝ)|^8311 ≤ (42770981151989/100000000000000 : ℝ)^6263
        have hw : |(2636401671/5000000000 : ℝ)|=(2636401671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_14 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369158949/10000000000 : ℝ)*x 0 + (5272803857/10000000000 : ℝ)*x 1 + (-2201088611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369158949/10000000000 : ℝ)^8311 ≤ (10952812679207/25000000000000 : ℝ)^6263 := by
    have hnat : (5369158949 : ℕ)^8311*25000000000000^6263 ≤ 10952812679207^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369158949 10000000000 10952812679207 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272803857/10000000000 : ℝ)^8311 ≤ (42770986695511/100000000000000 : ℝ)^6263 := by
    have hnat : (5272803857 : ℕ)^8311*100000000000000^6263 ≤ 42770986695511^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272803857 10000000000 42770986695511 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201088611/10000000000 : ℝ)^8311 ≤ (3354440643601/25000000000000 : ℝ)^6263 := by
    have hnat : (2201088611 : ℕ)^8311*25000000000000^6263 ≤ 3354440643601^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201088611 10000000000 3354440643601 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369158949/10000000000 : ℝ), (5272803857/10000000000 : ℝ), (-2201088611/10000000000 : ℝ)] ![(10952812679207/25000000000000 : ℝ), (42770986695511/100000000000000 : ℝ), (3354440643601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369158949/10000000000 : ℝ)|^8311 ≤ (10952812679207/25000000000000 : ℝ)^6263
        have hw : |(5369158949/10000000000 : ℝ)|=(5369158949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272803857/10000000000 : ℝ)|^8311 ≤ (42770986695511/100000000000000 : ℝ)^6263
        have hw : |(5272803857/10000000000 : ℝ)|=(5272803857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201088611/10000000000 : ℝ)|^8311 ≤ (3354440643601/25000000000000 : ℝ)^6263
        have hw : |(-2201088611/10000000000 : ℝ)|=(2201088611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_box_15 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16568743/39062500 : ℝ)*x 0 + (2216642401/5000000000 : ℝ)*x 1 + (886656671/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16568743/39062500 : ℝ)^8311 ≤ (32042894631869/100000000000000 : ℝ)^6263 := by
    have hnat : (16568743 : ℕ)^8311*100000000000000^6263 ≤ 32042894631869^6263*39062500^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16568743 39062500 32042894631869 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216642401/5000000000 : ℝ)^8311 ≤ (16989280017589/50000000000000 : ℝ)^6263 := by
    have hnat : (2216642401 : ℕ)^8311*50000000000000^6263 ≤ 16989280017589^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216642401 5000000000 16989280017589 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886656671/2000000000 : ℝ)^8311 ≤ (33978545318197/100000000000000 : ℝ)^6263 := by
    have hnat : (886656671 : ℕ)^8311*100000000000000^6263 ≤ 33978545318197^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886656671 2000000000 33978545318197 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16568743/39062500 : ℝ), (2216642401/5000000000 : ℝ), (886656671/2000000000 : ℝ)] ![(32042894631869/100000000000000 : ℝ), (16989280017589/50000000000000 : ℝ), (33978545318197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16568743/39062500 : ℝ)|^8311 ≤ (32042894631869/100000000000000 : ℝ)^6263
        have hw : |(16568743/39062500 : ℝ)|=(16568743/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2216642401/5000000000 : ℝ)|^8311 ≤ (16989280017589/50000000000000 : ℝ)^6263
        have hw : |(2216642401/5000000000 : ℝ)|=(2216642401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886656671/2000000000 : ℝ)|^8311 ≤ (33978545318197/100000000000000 : ℝ)^6263
        have hw : |(886656671/2000000000 : ℝ)|=(886656671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(741/1250 : ℝ) ∧ (15947/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8307/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11323/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (7249498367200729/50000000000000000000 : ℝ) := by
    have hpowers : (11323/100000 : ℝ)^4155 ≤ (7249498367200729/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11323 : ℕ)^4155*50000000000000000000^1024 ≤ 7249498367200729^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11323 100000 7249498367200729 50000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11323/100000 : ℝ)) (X := (7249498367200729/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (4155/1024 : ℝ) ≤ (34640877420498181/100000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^4155 ≤ (34640877420498181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7017 : ℕ)^4155*100000000000000000000^1024 ≤ 34640877420498181^1024*50000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 34640877420498181 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (34640877420498181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007249498367200729/25000000000000000000 : ℝ) ≤ (5000357288827739/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (25007249498367200729/25000000000000000000 : ℝ)^1024 ≤ (5000357288827739/5000000000000000 : ℝ)^4155 := by
      have hnat : (25007249498367200729 : ℕ)^1024*5000000000000000^4155 ≤ 5000357288827739^4155*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007249498367200729 25000000000000000000 5000357288827739 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357288827739/5000000000000000 : ℝ)) (X := (25007249498367200729/25000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049139874154899639/100000000000000000000 : ℝ) ≤ (1250151353542021/1250000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (100049139874154899639/100000000000000000000 : ℝ)^1024 ≤ (1250151353542021/1250000000000000 : ℝ)^4155 := by
      have hnat : (100049139874154899639 : ℕ)^1024*1250000000000000^4155 ≤ 1250151353542021^4155*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049139874154899639 100000000000000000000 1250151353542021 1250000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151353542021/1250000000000000 : ℝ)) (X := (100049139874154899639/100000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034640877420498181/50000000000000000000 : ℝ) ≤ (5000853539508429/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50034640877420498181/50000000000000000000 : ℝ)^1024 ≤ (5000853539508429/5000000000000000 : ℝ)^4155 := by
      have hnat : (50034640877420498181 : ℕ)^1024*5000000000000000^4155 ≤ 5000853539508429^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034640877420498181 50000000000000000000 5000853539508429 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000853539508429/5000000000000000 : ℝ)) (X := (50034640877420498181/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7249498367200729/50000000000000000000 : ℝ) ≤ ((13550349563554547559/13555000000000000000 : ℝ)+2*(49625068069/27110000000000 : ℝ)*(11323/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (13550349563554547559/13555000000000000000 : ℝ)+2*(49625068069/27110000000000 : ℝ)*(11323/100000 : ℝ)=(5000357288827739/5000000000000000 : ℝ) by norm_num, show 1+2*(7249498367200729/50000000000000000000 : ℝ)=(25007249498367200729/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34640877420498181/100000000000000000000 : ℝ)+(7249498367200729/50000000000000000000 : ℝ) ≤ ((13550349563554547559/13555000000000000000 : ℝ)+(49625068069/27110000000000 : ℝ)*((7017/50000 : ℝ)+(11323/100000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (13550349563554547559/13555000000000000000 : ℝ)+(49625068069/27110000000000 : ℝ)*((7017/50000 : ℝ)+(11323/100000 : ℝ))=(1250151353542021/1250000000000000 : ℝ) by norm_num, show 1+(34640877420498181/100000000000000000000 : ℝ)+(7249498367200729/50000000000000000000 : ℝ)=(100049139874154899639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34640877420498181/100000000000000000000 : ℝ) ≤ ((13550349563554547559/13555000000000000000 : ℝ)+2*(49625068069/27110000000000 : ℝ)*(7017/50000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (13550349563554547559/13555000000000000000 : ℝ)+2*(49625068069/27110000000000 : ℝ)*(7017/50000 : ℝ)=(5000853539508429/5000000000000000 : ℝ) by norm_num, show 1+2*(34640877420498181/100000000000000000000 : ℝ)=(50034640877420498181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13550349563554547559/13555000000000000000 : ℝ)*(X 1 0+X 2 0)+(49625068069/27110000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13550349563554547559/13555000000000000000 : ℝ)) (alpha := (49625068069/27110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13550349563554547559/13555000000000000000 : ℝ)*(X 0 1+X 2 1)+(49625068069/27110000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13550349563554547559/13555000000000000000 : ℝ)) (alpha := (49625068069/27110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13550349563554547559/13555000000000000000 : ℝ)*(X 0 2+X 1 2)+(49625068069/27110000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13550349563554547559/13555000000000000000 : ℝ)) (alpha := (49625068069/27110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256341953/1250000000 : ℝ)*X 0 0+(2688323421/5000000000 : ℝ)*X 0 1+(537664683/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059151373/2000000000 : ℝ)*X 1 0+(-432075149/2000000000 : ℝ)*X 1 1+(2688323327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323939179/2500000000 : ℝ)*X 2 0+(5376646729/10000000000 : ℝ)*X 2 1+(-2160375843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1118966157/2500000000 : ℝ)*X 0 0+(4316293903/10000000000 : ℝ)*X 0 1+(172651761/400000000 : ℝ)*X 0 2+(1118966157/2500000000 : ℝ)*X 1 0+(4316293903/10000000000 : ℝ)*X 1 1+(172651761/400000000 : ℝ)*X 1 2+(1118966157/2500000000 : ℝ)*X 2 0+(4316293903/10000000000 : ℝ)*X 2 1+(172651761/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18027243/78125000 : ℝ)*X 0 0+(2640415143/5000000000 : ℝ)*X 0 1+(2640415223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363487877/10000000000 : ℝ)*X 1 0+(-2197994539/10000000000 : ℝ)*X 1 1+(5280830321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536348743/1000000000 : ℝ)*X 2 0+(1320207539/2500000000 : ℝ)*X 2 1+(-2197995357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259919987/10000000000 : ℝ)*X 0 0+(2212122463/5000000000 : ℝ)*X 0 1+(4424245591/10000000000 : ℝ)*X 0 2+(4259919987/10000000000 : ℝ)*X 1 0+(2212122463/5000000000 : ℝ)*X 1 1+(4424245591/10000000000 : ℝ)*X 1 2+(4259919987/10000000000 : ℝ)*X 2 0+(2212122463/5000000000 : ℝ)*X 2 1+(4424245591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2253824601/10000000000 : ℝ)*X 0 0+(5215711999/10000000000 : ℝ)*X 0 1+(5386252959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644481539/5000000000 : ℝ)*X 1 0+(-539133549/2500000000 : ℝ)*X 1 1+(2693126473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288962929/10000000000 : ℝ)*X 2 0+(5386252409/10000000000 : ℝ)*X 2 1+(-26956689/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4497240891/10000000000 : ℝ)*X 0 0+(21527327/50000000 : ℝ)*X 0 1+(1076366309/2500000000 : ℝ)*X 0 2+(4497240891/10000000000 : ℝ)*X 1 0+(21527327/50000000 : ℝ)*X 1 1+(1076366309/2500000000 : ℝ)*X 1 2+(4497240891/10000000000 : ℝ)*X 2 0+(21527327/50000000 : ℝ)*X 2 1+(1076366309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-420946557/2000000000 : ℝ)*X 0 0+(340029351/625000000 : ℝ)*X 0 1+(527280327/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369159351/10000000000 : ℝ)*X 1 0+(-1100544379/5000000000 : ℝ)*X 1 1+(2636401671/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369158949/10000000000 : ℝ)*X 2 0+(5272803857/10000000000 : ℝ)*X 2 1+(-2201088611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((16568743/39062500 : ℝ)*X 0 0+(2216642401/5000000000 : ℝ)*X 0 1+(886656671/2000000000 : ℝ)*X 0 2+(16568743/39062500 : ℝ)*X 1 0+(2216642401/5000000000 : ℝ)*X 1 1+(886656671/2000000000 : ℝ)*X 1 2+(16568743/39062500 : ℝ)*X 2 0+(2216642401/5000000000 : ℝ)*X 2 1+(886656671/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-1686944487407126441206781283/2711000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188808667/100000000000000 : ℝ)*(upper1) + (58350213/10000000000000 : ℝ)*(lower4) + (65572633/50000000000000 : ℝ)*(upper5) + (975167501630141/25000000000000 : ℝ)*(major0) + (975167501630141/25000000000000 : ℝ)*(major1) + (975167501630141/25000000000000 : ℝ)*(major2) + (950639047/2500000000000 : ℝ)*(sp2) + (14024169683/100000000000000 : ℝ)*(sp3) + (650533954248373/12500000000000 : ℝ)*(sp4) + (5204117459737929/100000000000000 : ℝ)*(sp5) + (5204243978486883/100000000000000 : ℝ)*(sp6) + (1308892977825127/50000000000000 : ℝ)*(sp7) + (10370061779/100000000000000 : ℝ)*(sp12) + (82272155417/50000000000000 : ℝ)*(sp13) + (81806249369373/3125000000000 : ℝ)*(f.failure) + (5204282004048763/100000000000000 : ℝ)*(f.sum) + (80908068349/2711000000000000000000000000 : ℝ)*base66 + (1762321171341999181/338875000000000000000000000000000 : ℝ)*base68 + (2477160410462249181/338875000000000000000000000000000 : ℝ)*base70 + (3267079654292000819/338875000000000000000000000000000 : ℝ)*base71 + (18186477336859/1355500000000000000000000000 : ℝ)*base74 + (3456787120308874181/338875000000000000000000000000000 : ℝ)*base76 + (873378041487875819/338875000000000000000000000000000 : ℝ)*base77 + (1370059731685500819/338875000000000000000000000000000 : ℝ)*base79 + (8116775627533/1355500000000000000000000000 : ℝ)*base82 + (339137/62500000000000000000 : ℝ)*base90 + (339137/62500000000000000000 : ℝ)*base92 + (339137/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (741/1250 : ℝ) ≤ (100446958328774669428868136900387/169437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2553897/25000000000000 : ℝ)*(lower1) + (24514809/50000000000000 : ℝ)*(upper2) + (13257937/50000000000000 : ℝ)*(lower4) + (15349563/50000000000000 : ℝ)*(lower5) + (1982215917508731/50000000000000 : ℝ)*(major0) + (1982215917508731/50000000000000 : ℝ)*(major1) + (1982215917508731/50000000000000 : ℝ)*(major2) + (2624253542751903/50000000000000 : ℝ)*(sp0) + (1312112438038797/25000000000000 : ℝ)*(sp1) + (5248453663560243/100000000000000 : ℝ)*(sp2) + (2660591529239251/100000000000000 : ℝ)*(sp3) + (61521392719/100000000000000 : ℝ)*(sp9) + (3600624229/6250000000000 : ℝ)*(sp10) + (4188044101/100000000000000 : ℝ)*(sp12) + (2660591529239251/100000000000000 : ℝ)*(f.failure) + (5248511273547907/100000000000000 : ℝ)*(f.sum) + (28382682713067/2711000000000000000000000000 : ℝ)*base65 + (1983214288251012371/677750000000000000000000000000000 : ℝ)*base68 + (2417528690462012371/677750000000000000000000000000000 : ℝ)*base70 + (2682724000300762371/677750000000000000000000000000000 : ℝ)*base72 + (8681500043903/2711000000000000000000000000 : ℝ)*base74 + (7463916845421012371/677750000000000000000000000000000 : ℝ)*base76 + (2023737952208737629/677750000000000000000000000000000 : ℝ)*base77 + (2141307510477262371/677750000000000000000000000000000 : ℝ)*base80 + (267541918713/54220000000000000000000000 : ℝ)*base82 + (9392881/2000000000000000000000 : ℝ)*base89 + (9392881/2000000000000000000000 : ℝ)*base91 + (9392881/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (15947/20000 : ℝ) ≤ (108083494073184593467289597272449/135550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9013077/5000000000000 : ℝ)*(upper0) + (1286031/1000000000000 : ℝ)*(upper1) + (77801797/25000000000000 : ℝ)*(upper2) + (64459423/12500000000000 : ℝ)*(lower5) + (886496609881921/20000000000000 : ℝ)*(major0) + (886496609881921/20000000000000 : ℝ)*(major1) + (886496609881921/20000000000000 : ℝ)*(major2) + (329475104351/100000000000000 : ℝ)*(sp1) + (19201293819/20000000000000 : ℝ)*(sp3) + (18546616187/100000000000000 : ℝ)*(sp4) + (2931830307570779/50000000000000 : ℝ)*(sp8) + (2931674843326697/50000000000000 : ℝ)*(sp9) + (1172735832351549/20000000000000 : ℝ)*(sp10) + (743652983227631/25000000000000 : ℝ)*(sp11) + (2974707939379619/100000000000000 : ℝ)*(f.failure) + (1172735832351549/20000000000000 : ℝ)*(f.sum) + (829566586943/677750000000000000000000000 : ℝ)*base65 + (1518406043973380839/271100000000000000000000000000000 : ℝ)*base67 + (1510243425213980839/271100000000000000000000000000000 : ℝ)*base69 + (1459028750893180839/271100000000000000000000000000000 : ℝ)*base71 + (9182983135241/677750000000000000000000000 : ℝ)*base73 + (2092839831804580839/271100000000000000000000000000000 : ℝ)*base75 + (338130894599380839/271100000000000000000000000000000 : ℝ)*base77 + (5202908852944280839/271100000000000000000000000000000 : ℝ)*base79 + (15119225217161/2711000000000000000000000000 : ℝ)*base81 + (15450911/2000000000000000000000 : ℝ)*base90 + (15450911/2000000000000000000000 : ℝ)*base92 + (15450911/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8307/10000 : ℝ) ≤ (-2251971213147336683145170691/2711000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77863361/20000000000000 : ℝ)*(lower0) + (362853669/100000000000000 : ℝ)*(upper3) + (68810191/25000000000000 : ℝ)*(upper5) + (4467295813412049/100000000000000 : ℝ)*(major0) + (4467295813412049/100000000000000 : ℝ)*(major1) + (4467295813412049/100000000000000 : ℝ)*(major2) + (29916339/50000000000000 : ℝ)*(sp0) + (422749405593/100000000000000 : ℝ)*(sp5) + (119578962489/100000000000000 : ℝ)*(sp7) + (1657772243/100000000000000 : ℝ)*(sp8) + (5964207890869017/100000000000000 : ℝ)*(sp12) + (1192757371813669/20000000000000 : ℝ)*(sp13) + (2982104804236969/50000000000000 : ℝ)*(sp14) + (2997951744848711/100000000000000 : ℝ)*(sp15) + (936897288691/31250000000 : ℝ)*(f.failure) + (2982104804236969/50000000000000 : ℝ)*(f.sum) + (6679979489719/2711000000000000000000000000 : ℝ)*base66 + (48116925471299138391/1355500000000000000000000000000000 : ℝ)*base67 + (6524024552165861609/1355500000000000000000000000000000 : ℝ)*base70 + (21464115196138391/1355500000000000000000000000000000 : ℝ)*base71 + (46713803061573/2711000000000000000000000000 : ℝ)*base73 + (32385041065133861609/1355500000000000000000000000000000 : ℝ)*base76 + (387949286563138391/1355500000000000000000000000000000 : ℝ)*base77 + (34168356052236361609/1355500000000000000000000000000000 : ℝ)*base80 + (27492663361/10589843750000000000000000 : ℝ)*base81 + (3271/625000000000000000 : ℝ)*base89 + (3271/625000000000000000 : ℝ)*base91 + (3271/625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1118_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(741/1250 : ℝ) else (15947/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8307/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1118_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1118_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(741/1250 : ℝ) else (15947/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8307/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1118_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1118_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(741/1250 : ℝ) else (15947/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8307/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
