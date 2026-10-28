-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:24.949774+00:00
-- url     : https://prove2.me/submissions/6e44b583-2e07-4eff-b72c-a573ce1ad298

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
theorem support_rectangle_w1273_s0_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-925363067/5000000000 : ℝ)*x 0 + (1506080553/2500000000 : ℝ)*x 1 + (4796936311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925363067/5000000000 : ℝ)^8467 ≤ (10804025805863/100000000000000 : ℝ)^6419 := by
    have hnat : (925363067 : ℕ)^8467*100000000000000^6419 ≤ 10804025805863^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925363067 5000000000 10804025805863 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506080553/2500000000 : ℝ)^8467 ≤ (12812305649579/25000000000000 : ℝ)^6419 := by
    have hnat : (1506080553 : ℕ)^8467*25000000000000^6419 ≤ 12812305649579^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506080553 2500000000 12812305649579 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796936311/10000000000 : ℝ)^8467 ≤ (3794675158679/10000000000000 : ℝ)^6419 := by
    have hnat : (4796936311 : ℕ)^8467*10000000000000^6419 ≤ 3794675158679^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796936311 10000000000 3794675158679 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925363067/5000000000 : ℝ), (1506080553/2500000000 : ℝ), (4796936311/10000000000 : ℝ)] ![(10804025805863/100000000000000 : ℝ), (12812305649579/25000000000000 : ℝ), (3794675158679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925363067/5000000000 : ℝ)|^8467 ≤ (10804025805863/100000000000000 : ℝ)^6419
        have hw : |(-925363067/5000000000 : ℝ)|=(925363067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506080553/2500000000 : ℝ)|^8467 ≤ (12812305649579/25000000000000 : ℝ)^6419
        have hw : |(1506080553/2500000000 : ℝ)|=(1506080553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796936311/10000000000 : ℝ)|^8467 ≤ (3794675158679/10000000000000 : ℝ)^6419
        have hw : |(4796936311/10000000000 : ℝ)|=(4796936311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (220374273/400000000 : ℝ)*x 0 + (-1275771637/5000000000 : ℝ)*x 1 + (4796936281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220374273/400000000 : ℝ)^8467 ≤ (45551052458173/100000000000000 : ℝ)^6419 := by
    have hnat : (220374273 : ℕ)^8467*100000000000000^6419 ≤ 45551052458173^6419*400000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220374273 400000000 45551052458173 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275771637/5000000000 : ℝ)^8467 ≤ (132017570051/800000000000 : ℝ)^6419 := by
    have hnat : (1275771637 : ℕ)^8467*800000000000^6419 ≤ 132017570051^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275771637 5000000000 132017570051 800000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796936281/10000000000 : ℝ)^8467 ≤ (18973375636877/50000000000000 : ℝ)^6419 := by
    have hnat : (4796936281 : ℕ)^8467*50000000000000^6419 ≤ 18973375636877^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796936281 10000000000 18973375636877 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220374273/400000000 : ℝ), (-1275771637/5000000000 : ℝ), (4796936281/10000000000 : ℝ)] ![(45551052458173/100000000000000 : ℝ), (132017570051/800000000000 : ℝ), (18973375636877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220374273/400000000 : ℝ)|^8467 ≤ (45551052458173/100000000000000 : ℝ)^6419
        have hw : |(220374273/400000000 : ℝ)|=(220374273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1275771637/5000000000 : ℝ)|^8467 ≤ (132017570051/800000000000 : ℝ)^6419
        have hw : |(-1275771637/5000000000 : ℝ)|=(1275771637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796936281/10000000000 : ℝ)|^8467 ≤ (18973375636877/50000000000000 : ℝ)^6419
        have hw : |(4796936281/10000000000 : ℝ)|=(4796936281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2754678421/5000000000 : ℝ)*x 0 + (1199234071/2500000000 : ℝ)*x 1 + (-2551543247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754678421/5000000000 : ℝ)^8467 ≤ (11387763160893/25000000000000 : ℝ)^6419 := by
    have hnat : (2754678421 : ℕ)^8467*25000000000000^6419 ≤ 11387763160893^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754678421 5000000000 11387763160893 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199234071/2500000000 : ℝ)^8467 ≤ (18973375652529/50000000000000 : ℝ)^6419 := by
    have hnat : (1199234071 : ℕ)^8467*50000000000000^6419 ≤ 18973375652529^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199234071 2500000000 18973375652529 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2551543247/10000000000 : ℝ)^8467 ≤ (8251098013019/50000000000000 : ℝ)^6419 := by
    have hnat : (2551543247 : ℕ)^8467*50000000000000^6419 ≤ 8251098013019^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551543247 10000000000 8251098013019 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754678421/5000000000 : ℝ), (1199234071/2500000000 : ℝ), (-2551543247/10000000000 : ℝ)] ![(11387763160893/25000000000000 : ℝ), (18973375652529/50000000000000 : ℝ), (8251098013019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754678421/5000000000 : ℝ)|^8467 ≤ (11387763160893/25000000000000 : ℝ)^6419
        have hw : |(2754678421/5000000000 : ℝ)|=(2754678421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199234071/2500000000 : ℝ)|^8467 ≤ (18973375652529/50000000000000 : ℝ)^6419
        have hw : |(1199234071/2500000000 : ℝ)|=(1199234071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2551543247/10000000000 : ℝ)|^8467 ≤ (8251098013019/50000000000000 : ℝ)^6419
        have hw : |(-2551543247/10000000000 : ℝ)|=(2551543247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (523814953/1250000000 : ℝ)*x 0 + (3115733663/10000000000 : ℝ)*x 1 + (5620965693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523814953/1250000000 : ℝ)^8467 ≤ (31750559544749/100000000000000 : ℝ)^6419 := by
    have hnat : (523814953 : ℕ)^8467*100000000000000^6419 ≤ 31750559544749^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523814953 1250000000 31750559544749 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3115733663/10000000000 : ℝ)^8467 ≤ (21477282251459/100000000000000 : ℝ)^6419 := by
    have hnat : (3115733663 : ℕ)^8467*100000000000000^6419 ≤ 21477282251459^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115733663 10000000000 21477282251459 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620965693/10000000000 : ℝ)^8467 ≤ (46772158183731/100000000000000 : ℝ)^6419 := by
    have hnat : (5620965693 : ℕ)^8467*100000000000000^6419 ≤ 46772158183731^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620965693 10000000000 46772158183731 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523814953/1250000000 : ℝ), (3115733663/10000000000 : ℝ), (5620965693/10000000000 : ℝ)] ![(31750559544749/100000000000000 : ℝ), (21477282251459/100000000000000 : ℝ), (46772158183731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523814953/1250000000 : ℝ)|^8467 ≤ (31750559544749/100000000000000 : ℝ)^6419
        have hw : |(523814953/1250000000 : ℝ)|=(523814953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3115733663/10000000000 : ℝ)|^8467 ≤ (21477282251459/100000000000000 : ℝ)^6419
        have hw : |(3115733663/10000000000 : ℝ)|=(3115733663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620965693/10000000000 : ℝ)|^8467 ≤ (46772158183731/100000000000000 : ℝ)^6419
        have hw : |(5620965693/10000000000 : ℝ)|=(5620965693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-927746659/5000000000 : ℝ)*x 0 + (4828522519/10000000000 : ℝ)*x 1 + (2995809331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927746659/5000000000 : ℝ)^8467 ≤ (10840749458557/100000000000000 : ℝ)^6419 := by
    have hnat : (927746659 : ℕ)^8467*100000000000000^6419 ≤ 10840749458557^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927746659 5000000000 10840749458557 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4828522519/10000000000 : ℝ)^8467 ≤ (38276684470681/100000000000000 : ℝ)^6419 := by
    have hnat : (4828522519 : ℕ)^8467*100000000000000^6419 ≤ 38276684470681^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828522519 10000000000 38276684470681 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2995809331/5000000000 : ℝ)^8467 ≤ (50882566051341/100000000000000 : ℝ)^6419 := by
    have hnat : (2995809331 : ℕ)^8467*100000000000000^6419 ≤ 50882566051341^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995809331 5000000000 50882566051341 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927746659/5000000000 : ℝ), (4828522519/10000000000 : ℝ), (2995809331/5000000000 : ℝ)] ![(10840749458557/100000000000000 : ℝ), (38276684470681/100000000000000 : ℝ), (50882566051341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927746659/5000000000 : ℝ)|^8467 ≤ (10840749458557/100000000000000 : ℝ)^6419
        have hw : |(-927746659/5000000000 : ℝ)|=(927746659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4828522519/10000000000 : ℝ)|^8467 ≤ (38276684470681/100000000000000 : ℝ)^6419
        have hw : |(4828522519/10000000000 : ℝ)|=(4828522519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2995809331/5000000000 : ℝ)|^8467 ≤ (50882566051341/100000000000000 : ℝ)^6419
        have hw : |(2995809331/5000000000 : ℝ)|=(2995809331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587635701/5000000000 : ℝ)*x 0 + (-1356858411/10000000000 : ℝ)*x 1 + (1497905291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587635701/5000000000 : ℝ)^8467 ≤ (41943309080209/100000000000000 : ℝ)^6419 := by
    have hnat : (2587635701 : ℕ)^8467*100000000000000^6419 ≤ 41943309080209^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587635701 5000000000 41943309080209 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356858411/10000000000 : ℝ)^8467 ≤ (3587048414013/50000000000000 : ℝ)^6419 := by
    have hnat : (1356858411 : ℕ)^8467*50000000000000^6419 ≤ 3587048414013^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356858411 10000000000 3587048414013 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1497905291/2500000000 : ℝ)^8467 ≤ (12720648519549/25000000000000 : ℝ)^6419 := by
    have hnat : (1497905291 : ℕ)^8467*25000000000000^6419 ≤ 12720648519549^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1497905291 2500000000 12720648519549 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587635701/5000000000 : ℝ), (-1356858411/10000000000 : ℝ), (1497905291/2500000000 : ℝ)] ![(41943309080209/100000000000000 : ℝ), (3587048414013/50000000000000 : ℝ), (12720648519549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587635701/5000000000 : ℝ)|^8467 ≤ (41943309080209/100000000000000 : ℝ)^6419
        have hw : |(2587635701/5000000000 : ℝ)|=(2587635701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1356858411/10000000000 : ℝ)|^8467 ≤ (3587048414013/50000000000000 : ℝ)^6419
        have hw : |(-1356858411/10000000000 : ℝ)|=(1356858411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1497905291/2500000000 : ℝ)|^8467 ≤ (12720648519549/25000000000000 : ℝ)^6419
        have hw : |(1497905291/2500000000 : ℝ)|=(1497905291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5175272543/10000000000 : ℝ)*x 0 + (2995809537/5000000000 : ℝ)*x 1 + (-1356860019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175272543/10000000000 : ℝ)^8467 ≤ (20971660638947/50000000000000 : ℝ)^6419 := by
    have hnat : (5175272543 : ℕ)^8467*50000000000000^6419 ≤ 20971660638947^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175272543 10000000000 20971660638947 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995809537/5000000000 : ℝ)^8467 ≤ (2035302826659/4000000000000 : ℝ)^6419 := by
    have hnat : (2995809537 : ℕ)^8467*4000000000000^6419 ≤ 2035302826659^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995809537 5000000000 2035302826659 4000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356860019/10000000000 : ℝ)^8467 ≤ (3587054021277/50000000000000 : ℝ)^6419 := by
    have hnat : (1356860019 : ℕ)^8467*50000000000000^6419 ≤ 3587054021277^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356860019 10000000000 3587054021277 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175272543/10000000000 : ℝ), (2995809537/5000000000 : ℝ), (-1356860019/10000000000 : ℝ)] ![(20971660638947/50000000000000 : ℝ), (2035302826659/4000000000000 : ℝ), (3587054021277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175272543/10000000000 : ℝ)|^8467 ≤ (20971660638947/50000000000000 : ℝ)^6419
        have hw : |(5175272543/10000000000 : ℝ)|=(5175272543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995809537/5000000000 : ℝ)|^8467 ≤ (2035302826659/4000000000000 : ℝ)^6419
        have hw : |(2995809537/5000000000 : ℝ)|=(2995809537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1356860019/10000000000 : ℝ)|^8467 ≤ (3587054021277/50000000000000 : ℝ)^6419
        have hw : |(-1356860019/10000000000 : ℝ)|=(1356860019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s0_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200253271/10000000000 : ℝ)*x 0 + (1389125251/2500000000 : ℝ)*x 1 + (1591239457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200253271/10000000000 : ℝ)^8467 ≤ (31847875061159/100000000000000 : ℝ)^6419 := by
    have hnat : (4200253271 : ℕ)^8467*100000000000000^6419 ≤ 31847875061159^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200253271 10000000000 31847875061159 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389125251/2500000000 : ℝ)^8467 ≤ (2303295025549/5000000000000 : ℝ)^6419 := by
    have hnat : (1389125251 : ℕ)^8467*5000000000000^6419 ≤ 2303295025549^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389125251 2500000000 2303295025549 5000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591239457/5000000000 : ℝ)^8467 ≤ (22086224408991/100000000000000 : ℝ)^6419 := by
    have hnat : (1591239457 : ℕ)^8467*100000000000000^6419 ≤ 22086224408991^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591239457 5000000000 22086224408991 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200253271/10000000000 : ℝ), (1389125251/2500000000 : ℝ), (1591239457/5000000000 : ℝ)] ![(31847875061159/100000000000000 : ℝ), (2303295025549/5000000000000 : ℝ), (22086224408991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200253271/10000000000 : ℝ)|^8467 ≤ (31847875061159/100000000000000 : ℝ)^6419
        have hw : |(4200253271/10000000000 : ℝ)|=(4200253271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1389125251/2500000000 : ℝ)|^8467 ≤ (2303295025549/5000000000000 : ℝ)^6419
        have hw : |(1389125251/2500000000 : ℝ)|=(1389125251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1591239457/5000000000 : ℝ)|^8467 ≤ (22086224408991/100000000000000 : ℝ)^6419
        have hw : |(1591239457/5000000000 : ℝ)|=(1591239457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (189/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27317/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4233/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4233 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4233*1^1024 ≤ 0^1024*1^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4233/1024 : ℝ) ≤ (452928803762804303/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4233 ≤ (452928803762804303/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4233*20000000000000000000^1024 ≤ 452928803762804303^1024*5^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 452928803762804303 20000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (452928803762804303/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4233 := by
      have hnat : (1 : ℕ)^1024*1^4233 ≤ 1^4233*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20452928803762804303/20000000000000000000 : ℝ) ≤ (5027159807126281/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (20452928803762804303/20000000000000000000 : ℝ)^1024 ≤ (5027159807126281/5000000000000000 : ℝ)^4233 := by
      have hnat : (20452928803762804303 : ℕ)^1024*5000000000000000^4233 ≤ 5027159807126281^4233*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20452928803762804303 20000000000000000000 5027159807126281 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027159807126281/5000000000000000 : ℝ)) (X := (20452928803762804303/20000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10452928803762804303/10000000000000000000 : ℝ) ≤ (2527159807126281/2500000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (10452928803762804303/10000000000000000000 : ℝ)^1024 ≤ (2527159807126281/2500000000000000 : ℝ)^4233 := by
      have hnat : (10452928803762804303 : ℕ)^1024*2500000000000000^4233 ≤ 2527159807126281^4233*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10452928803762804303 10000000000000000000 2527159807126281 2500000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527159807126281/2500000000000000 : ℝ)) (X := (10452928803762804303/10000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27159807126281/2000000000000000 : ℝ)*(0 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27159807126281/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(452928803762804303/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27159807126281/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27159807126281/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027159807126281/5000000000000000 : ℝ) by norm_num, show 1+(452928803762804303/20000000000000000000 : ℝ)+(0 : ℝ)=(20452928803762804303/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(452928803762804303/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27159807126281/2000000000000000 : ℝ)*(2/5 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27159807126281/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527159807126281/2500000000000000 : ℝ) by norm_num, show 1+2*(452928803762804303/20000000000000000000 : ℝ)=(10452928803762804303/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27159807126281/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27159807126281/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27159807126281/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27159807126281/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27159807126281/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27159807126281/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-925363067/5000000000 : ℝ)*X 0 0+(1506080553/2500000000 : ℝ)*X 0 1+(4796936311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((220374273/400000000 : ℝ)*X 1 0+(-1275771637/5000000000 : ℝ)*X 1 1+(4796936281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754678421/5000000000 : ℝ)*X 2 0+(1199234071/2500000000 : ℝ)*X 2 1+(-2551543247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((523814953/1250000000 : ℝ)*X 0 0+(3115733663/10000000000 : ℝ)*X 0 1+(5620965693/10000000000 : ℝ)*X 0 2+(523814953/1250000000 : ℝ)*X 1 0+(3115733663/10000000000 : ℝ)*X 1 1+(5620965693/10000000000 : ℝ)*X 1 2+(523814953/1250000000 : ℝ)*X 2 0+(3115733663/10000000000 : ℝ)*X 2 1+(5620965693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-927746659/5000000000 : ℝ)*X 0 0+(4828522519/10000000000 : ℝ)*X 0 1+(2995809331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587635701/5000000000 : ℝ)*X 1 0+(-1356858411/10000000000 : ℝ)*X 1 1+(1497905291/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175272543/10000000000 : ℝ)*X 2 0+(2995809537/5000000000 : ℝ)*X 2 1+(-1356860019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4200253271/10000000000 : ℝ)*X 0 0+(1389125251/2500000000 : ℝ)*X 0 1+(1591239457/5000000000 : ℝ)*X 0 2+(4200253271/10000000000 : ℝ)*X 1 0+(1389125251/2500000000 : ℝ)*X 1 1+(1591239457/5000000000 : ℝ)*X 1 2+(4200253271/10000000000 : ℝ)*X 2 0+(1389125251/2500000000 : ℝ)*X 2 1+(1591239457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120974584029583376896653/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31728517/100000000000000 : ℝ)*(base1) + (23700919/4000000000000 : ℝ)*(base19) + (297518497/50000000000000 : ℝ)*(base23) + (65335053/100000000000000 : ℝ)*(upper3) + (72657971/100000000000000 : ℝ)*(upper5) + (606954880100557/100000000000000 : ℝ)*(major0) + (606954880100557/100000000000000 : ℝ)*(major1) + (606954880100557/100000000000000 : ℝ)*(major2) + (162948284619801/20000000000000 : ℝ)*(sp0) + (50921417791009/6250000000000 : ℝ)*(sp1) + (6517941457137/800000000000 : ℝ)*(sp2) + (49895685344779/12500000000000 : ℝ)*(sp3) + (1885808631/100000000000000 : ℝ)*(sp4) + (443942759/50000000000000 : ℝ)*(sp7) + (399166402372267/100000000000000 : ℝ)*(f.failure) + (814743277179119/100000000000000 : ℝ)*(f.sum) + (104718504361483/100000000000000000000000000000 : ℝ)*base66 + (1210370409961483/200000000000000000000000000000 : ℝ)*base68 + (1433882423561483/200000000000000000000000000000 : ℝ)*base70 + (1026304911761483/200000000000000000000000000000 : ℝ)*base72 + (313158365761483/100000000000000000000000000000 : ℝ)*base74 + (1727966060961483/200000000000000000000000000000 : ℝ)*base76 + (598422201761483/200000000000000000000000000000 : ℝ)*base78 + (1460911000161483/200000000000000000000000000000 : ℝ)*base80 + (624905757861483/100000000000000000000000000000 : ℝ)*base82 + (10837999/10000000000000000000000 : ℝ)*base90 + (10837999/10000000000000000000000 : ℝ)*base92 + (10837999/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425340179415678843/62500000000000000000000 : ℝ) := by norm_num
    linear_combination (30578803/10000000000000 : ℝ)*(base1) + (1433348739/100000000000000 : ℝ)*(base19) + (806755477/50000000000000 : ℝ)*(base23) + (310862207/100000000000000 : ℝ)*(upper3) + (80062468801493/12500000000000 : ℝ)*(major0) + (80062468801493/12500000000000 : ℝ)*(major1) + (80062468801493/12500000000000 : ℝ)*(major2) + (123704873/5000000000000 : ℝ)*(sp1) + (1164302401/50000000000000 : ℝ)*(sp2) + (10891497/50000000000000 : ℝ)*(sp3) + (859772253854661/100000000000000 : ℝ)*(sp4) + (53735502538777/6250000000000 : ℝ)*(sp5) + (429884002975437/50000000000000 : ℝ)*(sp6) + (421226998338133/100000000000000 : ℝ)*(sp7) + (421227325909157/100000000000000 : ℝ)*(f.failure) + (859771948066631/100000000000000 : ℝ)*(f.sum) + (1374203924967/12500000000000000000000000000 : ℝ)*base66 + (9206482012533/25000000000000000000000000000 : ℝ)*base67 + (99253827312467/25000000000000000000000000000 : ℝ)*base70 + (99095614237467/25000000000000000000000000000 : ℝ)*base72 + (15669885312533/12500000000000000000000000000 : ℝ)*base73 + (91179034537533/25000000000000000000000000000 : ℝ)*base75 + (50925443212533/25000000000000000000000000000 : ℝ)*base77 + (189601597387533/25000000000000000000000000000 : ℝ)*base79 + (70133848962467/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9143329/10000000000000000000000 : ℝ)*base90 + (9143329/10000000000000000000000 : ℝ)*base92 + (9143329/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s1_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-409161061/2000000000 : ℝ)*x 0 + (5667659879/10000000000 : ℝ)*x 1 + (251436191/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409161061/2000000000 : ℝ)^8467 ≤ (2466173423717/20000000000000 : ℝ)^6419 := by
    have hnat : (409161061 : ℕ)^8467*20000000000000^6419 ≤ 2466173423717^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409161061 2000000000 2466173423717 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5667659879/10000000000 : ℝ)^8467 ≤ (9457069011197/20000000000000 : ℝ)^6419 := by
    have hnat : (5667659879 : ℕ)^8467*20000000000000^6419 ≤ 9457069011197^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667659879 10000000000 9457069011197 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251436191/500000000 : ℝ)^8467 ≤ (20191893904647/50000000000000 : ℝ)^6419 := by
    have hnat : (251436191 : ℕ)^8467*50000000000000^6419 ≤ 20191893904647^6419*500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251436191 500000000 20191893904647 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409161061/2000000000 : ℝ), (5667659879/10000000000 : ℝ), (251436191/500000000 : ℝ)] ![(2466173423717/20000000000000 : ℝ), (9457069011197/20000000000000 : ℝ), (20191893904647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409161061/2000000000 : ℝ)|^8467 ≤ (2466173423717/20000000000000 : ℝ)^6419
        have hw : |(-409161061/2000000000 : ℝ)|=(409161061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5667659879/10000000000 : ℝ)|^8467 ≤ (9457069011197/20000000000000 : ℝ)^6419
        have hw : |(5667659879/10000000000 : ℝ)|=(5667659879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251436191/500000000 : ℝ)|^8467 ≤ (20191893904647/50000000000000 : ℝ)^6419
        have hw : |(251436191/500000000 : ℝ)|=(251436191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541192603/1000000000 : ℝ)*x 0 + (-597096787/2500000000 : ℝ)*x 1 + (5028723619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541192603/1000000000 : ℝ)^8467 ≤ (11122874044803/25000000000000 : ℝ)^6419 := by
    have hnat : (541192603 : ℕ)^8467*25000000000000^6419 ≤ 11122874044803^6419*1000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541192603 1000000000 11122874044803 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597096787/2500000000 : ℝ)^8467 ≤ (3781179530597/25000000000000 : ℝ)^6419 := by
    have hnat : (597096787 : ℕ)^8467*25000000000000^6419 ≤ 3781179530597^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597096787 2500000000 3781179530597 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028723619/10000000000 : ℝ)^8467 ≤ (40383785680137/100000000000000 : ℝ)^6419 := by
    have hnat : (5028723619 : ℕ)^8467*100000000000000^6419 ≤ 40383785680137^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028723619 10000000000 40383785680137 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541192603/1000000000 : ℝ), (-597096787/2500000000 : ℝ), (5028723619/10000000000 : ℝ)] ![(11122874044803/25000000000000 : ℝ), (3781179530597/25000000000000 : ℝ), (40383785680137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541192603/1000000000 : ℝ)|^8467 ≤ (11122874044803/25000000000000 : ℝ)^6419
        have hw : |(541192603/1000000000 : ℝ)|=(541192603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-597096787/2500000000 : ℝ)|^8467 ≤ (3781179530597/25000000000000 : ℝ)^6419
        have hw : |(-597096787/2500000000 : ℝ)|=(597096787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028723619/10000000000 : ℝ)|^8467 ≤ (40383785680137/100000000000000 : ℝ)^6419
        have hw : |(5028723619/10000000000 : ℝ)|=(5028723619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5411925801/10000000000 : ℝ)*x 0 + (5028723817/10000000000 : ℝ)*x 1 + (-1194193597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411925801/10000000000 : ℝ)^8467 ≤ (44491493695949/100000000000000 : ℝ)^6419 := by
    have hnat : (5411925801 : ℕ)^8467*100000000000000^6419 ≤ 44491493695949^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411925801 10000000000 44491493695949 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5028723817/10000000000 : ℝ)^8467 ≤ (8076757555503/20000000000000 : ℝ)^6419 := by
    have hnat : (5028723817 : ℕ)^8467*20000000000000^6419 ≤ 8076757555503^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028723817 10000000000 8076757555503 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194193597/5000000000 : ℝ)^8467 ≤ (3781179626657/25000000000000 : ℝ)^6419 := by
    have hnat : (1194193597 : ℕ)^8467*25000000000000^6419 ≤ 3781179626657^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194193597 5000000000 3781179626657 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411925801/10000000000 : ℝ), (5028723817/10000000000 : ℝ), (-1194193597/5000000000 : ℝ)] ![(44491493695949/100000000000000 : ℝ), (8076757555503/20000000000000 : ℝ), (3781179626657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411925801/10000000000 : ℝ)|^8467 ≤ (44491493695949/100000000000000 : ℝ)^6419
        have hw : |(5411925801/10000000000 : ℝ)|=(5411925801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5028723817/10000000000 : ℝ)|^8467 ≤ (8076757555503/20000000000000 : ℝ)^6419
        have hw : |(5028723817/10000000000 : ℝ)|=(5028723817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194193597/5000000000 : ℝ)|^8467 ≤ (3781179626657/25000000000000 : ℝ)^6419
        have hw : |(-1194193597/5000000000 : ℝ)|=(1194193597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4306065929/10000000000 : ℝ)*x 0 + (3701173727/10000000000 : ℝ)*x 1 + (1001062761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306065929/10000000000 : ℝ)^8467 ≤ (32910394274461/100000000000000 : ℝ)^6419 := by
    have hnat : (4306065929 : ℕ)^8467*100000000000000^6419 ≤ 32910394274461^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306065929 10000000000 32910394274461 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3701173727/10000000000 : ℝ)^8467 ≤ (5390722307799/20000000000000 : ℝ)^6419 := by
    have hnat : (3701173727 : ℕ)^8467*20000000000000^6419 ≤ 5390722307799^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701173727 10000000000 5390722307799 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001062761/2000000000 : ℝ)^8467 ≤ (40135994167711/100000000000000 : ℝ)^6419 := by
    have hnat : (1001062761 : ℕ)^8467*100000000000000^6419 ≤ 40135994167711^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001062761 2000000000 40135994167711 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306065929/10000000000 : ℝ), (3701173727/10000000000 : ℝ), (1001062761/2000000000 : ℝ)] ![(32910394274461/100000000000000 : ℝ), (5390722307799/20000000000000 : ℝ), (40135994167711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306065929/10000000000 : ℝ)|^8467 ≤ (32910394274461/100000000000000 : ℝ)^6419
        have hw : |(4306065929/10000000000 : ℝ)|=(4306065929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3701173727/10000000000 : ℝ)|^8467 ≤ (5390722307799/20000000000000 : ℝ)^6419
        have hw : |(3701173727/10000000000 : ℝ)|=(3701173727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001062761/2000000000 : ℝ)|^8467 ≤ (40135994167711/100000000000000 : ℝ)^6419
        have hw : |(1001062761/2000000000 : ℝ)|=(1001062761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-51161123/250000000 : ℝ)*x 0 + (5037012003/10000000000 : ℝ)*x 1 + (2829607907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51161123/250000000 : ℝ)^8467 ≤ (616797629841/5000000000000 : ℝ)^6419 := by
    have hnat : (51161123 : ℕ)^8467*5000000000000^6419 ≤ 616797629841^6419*250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51161123 250000000 616797629841 5000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037012003/10000000000 : ℝ)^8467 ≤ (1618864243453/4000000000000 : ℝ)^6419 := by
    have hnat : (5037012003 : ℕ)^8467*4000000000000^6419 ≤ 1618864243453^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037012003 10000000000 1618864243453 4000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829607907/5000000000 : ℝ)^8467 ≤ (5899055162643/12500000000000 : ℝ)^6419 := by
    have hnat : (2829607907 : ℕ)^8467*12500000000000^6419 ≤ 5899055162643^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829607907 5000000000 5899055162643 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51161123/250000000 : ℝ), (5037012003/10000000000 : ℝ), (2829607907/5000000000 : ℝ)] ![(616797629841/5000000000000 : ℝ), (1618864243453/4000000000000 : ℝ), (5899055162643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51161123/250000000 : ℝ)|^8467 ≤ (616797629841/5000000000000 : ℝ)^6419
        have hw : |(-51161123/250000000 : ℝ)|=(51161123/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037012003/10000000000 : ℝ)|^8467 ≤ (1618864243453/4000000000000 : ℝ)^6419
        have hw : |(5037012003/10000000000 : ℝ)|=(5037012003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829607907/5000000000 : ℝ)|^8467 ≤ (5899055162643/12500000000000 : ℝ)^6419
        have hw : |(2829607907/5000000000 : ℝ)|=(2829607907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1311767771/2500000000 : ℝ)*x 0 + (-1757894767/10000000000 : ℝ)*x 1 + (1131843283/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311767771/2500000000 : ℝ)^8467 ≤ (42712565951581/100000000000000 : ℝ)^6419 := by
    have hnat : (1311767771 : ℕ)^8467*100000000000000^6419 ≤ 42712565951581^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311767771 2500000000 42712565951581 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1757894767/10000000000 : ℝ)^8467 ≤ (1009498612777/10000000000000 : ℝ)^6419 := by
    have hnat : (1757894767 : ℕ)^8467*10000000000000^6419 ≤ 1009498612777^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757894767 10000000000 1009498612777 10000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131843283/2000000000 : ℝ)^8467 ≤ (23596223955963/50000000000000 : ℝ)^6419 := by
    have hnat : (1131843283 : ℕ)^8467*50000000000000^6419 ≤ 23596223955963^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131843283 2000000000 23596223955963 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311767771/2500000000 : ℝ), (-1757894767/10000000000 : ℝ), (1131843283/2000000000 : ℝ)] ![(42712565951581/100000000000000 : ℝ), (1009498612777/10000000000000 : ℝ), (23596223955963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311767771/2500000000 : ℝ)|^8467 ≤ (42712565951581/100000000000000 : ℝ)^6419
        have hw : |(1311767771/2500000000 : ℝ)|=(1311767771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1757894767/10000000000 : ℝ)|^8467 ≤ (1009498612777/10000000000000 : ℝ)^6419
        have hw : |(-1757894767/10000000000 : ℝ)|=(1757894767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131843283/2000000000 : ℝ)|^8467 ≤ (23596223955963/50000000000000 : ℝ)^6419
        have hw : |(1131843283/2000000000 : ℝ)|=(1131843283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5247071/10000000 : ℝ)*x 0 + (88425251/156250000 : ℝ)*x 1 + (-351579079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247071/10000000 : ℝ)^8467 ≤ (8542513009927/20000000000000 : ℝ)^6419 := by
    have hnat : (5247071 : ℕ)^8467*20000000000000^6419 ≤ 8542513009927^6419*10000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247071 10000000 8542513009927 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88425251/156250000 : ℝ)^8467 ≤ (47192444051053/100000000000000 : ℝ)^6419 := by
    have hnat : (88425251 : ℕ)^8467*100000000000000^6419 ≤ 47192444051053^6419*156250000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88425251 156250000 47192444051053 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351579079/2000000000 : ℝ)^8467 ≤ (10094990884787/100000000000000 : ℝ)^6419 := by
    have hnat : (351579079 : ℕ)^8467*100000000000000^6419 ≤ 10094990884787^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351579079 2000000000 10094990884787 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247071/10000000 : ℝ), (88425251/156250000 : ℝ), (-351579079/2000000000 : ℝ)] ![(8542513009927/20000000000000 : ℝ), (47192444051053/100000000000000 : ℝ), (10094990884787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247071/10000000 : ℝ)|^8467 ≤ (8542513009927/20000000000000 : ℝ)^6419
        have hw : |(5247071/10000000 : ℝ)|=(5247071/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88425251/156250000 : ℝ)|^8467 ≤ (47192444051053/100000000000000 : ℝ)^6419
        have hw : |(88425251/156250000 : ℝ)|=(88425251/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-351579079/2000000000 : ℝ)|^8467 ≤ (10094990884787/100000000000000 : ℝ)^6419
        have hw : |(-351579079/2000000000 : ℝ)|=(351579079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s1_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4307370777/10000000000 : ℝ)*x 0 + (4988396917/10000000000 : ℝ)*x 1 + (1859204263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307370777/10000000000 : ℝ)^8467 ≤ (16461774707783/50000000000000 : ℝ)^6419 := by
    have hnat : (4307370777 : ℕ)^8467*50000000000000^6419 ≤ 16461774707783^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307370777 10000000000 16461774707783 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988396917/10000000000 : ℝ)^8467 ≤ (9989289951087/25000000000000 : ℝ)^6419 := by
    have hnat : (4988396917 : ℕ)^8467*25000000000000^6419 ≤ 9989289951087^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988396917 10000000000 9989289951087 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859204263/5000000000 : ℝ)^8467 ≤ (27119290764497/100000000000000 : ℝ)^6419 := by
    have hnat : (1859204263 : ℕ)^8467*100000000000000^6419 ≤ 27119290764497^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859204263 5000000000 27119290764497 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307370777/10000000000 : ℝ), (4988396917/10000000000 : ℝ), (1859204263/5000000000 : ℝ)] ![(16461774707783/50000000000000 : ℝ), (9989289951087/25000000000000 : ℝ), (27119290764497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307370777/10000000000 : ℝ)|^8467 ≤ (16461774707783/50000000000000 : ℝ)^6419
        have hw : |(4307370777/10000000000 : ℝ)|=(4307370777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988396917/10000000000 : ℝ)|^8467 ≤ (9989289951087/25000000000000 : ℝ)^6419
        have hw : |(4988396917/10000000000 : ℝ)|=(4988396917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859204263/5000000000 : ℝ)|^8467 ≤ (27119290764497/100000000000000 : ℝ)^6419
        have hw : |(1859204263/5000000000 : ℝ)|=(1859204263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (6357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3973/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (189/20000 : ℝ) ^ (4233/1024 : ℝ) ≤ (106856799511/25000000000000000000 : ℝ) := by
    have hpowers : (189/20000 : ℝ)^4233 ≤ (106856799511/25000000000000000000 : ℝ)^1024 := by
      have hnat : (189 : ℕ)^4233*25000000000000000000^1024 ≤ 106856799511^1024*20000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 20000 106856799511 25000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/20000 : ℝ)) (X := (106856799511/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27317/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (117023455811041313/25000000000000000000 : ℝ) := by
    have hpowers : (27317/100000 : ℝ)^4233 ≤ (117023455811041313/25000000000000000000 : ℝ)^1024 := by
      have hnat : (27317 : ℕ)^4233*25000000000000000000^1024 ≤ 117023455811041313^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27317 100000 117023455811041313 25000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27317/100000 : ℝ)) (X := (117023455811041313/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000106856799511/12500000000000000000 : ℝ) ≤ (5000000010339841/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (12500000106856799511/12500000000000000000 : ℝ)^1024 ≤ (5000000010339841/5000000000000000 : ℝ)^4233 := by
      have hnat : (12500000106856799511 : ℕ)^1024*5000000000000000^4233 ≤ 5000000010339841^4233*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000106856799511 12500000000000000000 5000000010339841 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000010339841/5000000000000000 : ℝ)) (X := (12500000106856799511/12500000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3139627945333480103/3125000000000000000 : ℝ) ≤ (2002260715190531/2000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (3139627945333480103/3125000000000000000 : ℝ)^1024 ≤ (2002260715190531/2000000000000000 : ℝ)^4233 := by
      have hnat : (3139627945333480103 : ℕ)^1024*2000000000000000^4233 ≤ 2002260715190531^4233*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3139627945333480103 3125000000000000000 2002260715190531 2000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002260715190531/2000000000000000 : ℝ)) (X := (3139627945333480103/3125000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12617023455811041313/12500000000000000000 : ℝ) ≤ (2505651782806407/2500000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (12617023455811041313/12500000000000000000 : ℝ)^1024 ≤ (2505651782806407/2500000000000000 : ℝ)^4233 := by
      have hnat : (12617023455811041313 : ℕ)^1024*2500000000000000^4233 ≤ 2505651782806407^4233*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12617023455811041313 12500000000000000000 2505651782806407 2500000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505651782806407/2500000000000000 : ℝ)) (X := (12617023455811041313/12500000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(106856799511/25000000000000000000 : ℝ) ≤ ((131849318412949327367/131860000000000000000 : ℝ)+2*(11303555272973/2637200000000000 : ℝ)*(189/20000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (131849318412949327367/131860000000000000000 : ℝ)+2*(11303555272973/2637200000000000 : ℝ)*(189/20000 : ℝ)=(5000000010339841/5000000000000000 : ℝ) by norm_num, show 1+2*(106856799511/25000000000000000000 : ℝ)=(12500000106856799511/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117023455811041313/25000000000000000000 : ℝ)+(106856799511/25000000000000000000 : ℝ) ≤ ((131849318412949327367/131860000000000000000 : ℝ)+(11303555272973/2637200000000000 : ℝ)*((27317/100000 : ℝ)+(189/20000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (131849318412949327367/131860000000000000000 : ℝ)+(11303555272973/2637200000000000 : ℝ)*((27317/100000 : ℝ)+(189/20000 : ℝ))=(2002260715190531/2000000000000000 : ℝ) by norm_num, show 1+(117023455811041313/25000000000000000000 : ℝ)+(106856799511/25000000000000000000 : ℝ)=(3139627945333480103/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117023455811041313/25000000000000000000 : ℝ) ≤ ((131849318412949327367/131860000000000000000 : ℝ)+2*(11303555272973/2637200000000000 : ℝ)*(27317/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (131849318412949327367/131860000000000000000 : ℝ)+2*(11303555272973/2637200000000000 : ℝ)*(27317/100000 : ℝ)=(2505651782806407/2500000000000000 : ℝ) by norm_num, show 1+2*(117023455811041313/25000000000000000000 : ℝ)=(12617023455811041313/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131849318412949327367/131860000000000000000 : ℝ)*(X 1 0+X 2 0)+(11303555272973/2637200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (189/20000 : ℝ)) (hi := (27317/100000 : ℝ)) (c := (131849318412949327367/131860000000000000000 : ℝ)) (alpha := (11303555272973/2637200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131849318412949327367/131860000000000000000 : ℝ)*(X 0 1+X 2 1)+(11303555272973/2637200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (189/20000 : ℝ)) (hi := (27317/100000 : ℝ)) (c := (131849318412949327367/131860000000000000000 : ℝ)) (alpha := (11303555272973/2637200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131849318412949327367/131860000000000000000 : ℝ)*(X 0 2+X 1 2)+(11303555272973/2637200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (189/20000 : ℝ)) (hi := (27317/100000 : ℝ)) (c := (131849318412949327367/131860000000000000000 : ℝ)) (alpha := (11303555272973/2637200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409161061/2000000000 : ℝ)*X 0 0+(5667659879/10000000000 : ℝ)*X 0 1+(251436191/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541192603/1000000000 : ℝ)*X 1 0+(-597096787/2500000000 : ℝ)*X 1 1+(5028723619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411925801/10000000000 : ℝ)*X 2 0+(5028723817/10000000000 : ℝ)*X 2 1+(-1194193597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306065929/10000000000 : ℝ)*X 0 0+(3701173727/10000000000 : ℝ)*X 0 1+(1001062761/2000000000 : ℝ)*X 0 2+(4306065929/10000000000 : ℝ)*X 1 0+(3701173727/10000000000 : ℝ)*X 1 1+(1001062761/2000000000 : ℝ)*X 1 2+(4306065929/10000000000 : ℝ)*X 2 0+(3701173727/10000000000 : ℝ)*X 2 1+(1001062761/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51161123/250000000 : ℝ)*X 0 0+(5037012003/10000000000 : ℝ)*X 0 1+(2829607907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311767771/2500000000 : ℝ)*X 1 0+(-1757894767/10000000000 : ℝ)*X 1 1+(1131843283/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5247071/10000000 : ℝ)*X 2 0+(88425251/156250000 : ℝ)*X 2 1+(-351579079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307370777/10000000000 : ℝ)*X 0 0+(4988396917/10000000000 : ℝ)*X 0 1+(1859204263/5000000000 : ℝ)*X 0 2+(4307370777/10000000000 : ℝ)*X 1 0+(4988396917/10000000000 : ℝ)*X 1 1+(1859204263/5000000000 : ℝ)*X 1 2+(4307370777/10000000000 : ℝ)*X 2 0+(4988396917/10000000000 : ℝ)*X 2 1+(1859204263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1667501928120851032152956931/412062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47645393/100000000000000 : ℝ)*(base1) + (840612543/100000000000000 : ℝ)*(base19) + (387193279/50000000000000 : ℝ)*(base23) + (99399317/100000000000000 : ℝ)*(upper3) + (65071581/100000000000000 : ℝ)*(upper5) + (145743986194331/12500000000000 : ℝ)*(major0) + (145743986194331/12500000000000 : ℝ)*(major1) + (145743986194331/12500000000000 : ℝ)*(major2) + (782553203888099/50000000000000 : ℝ)*(sp0) + (1565109692039719/100000000000000 : ℝ)*(sp1) + (195638719783213/12500000000000 : ℝ)*(sp2) + (383395428810257/50000000000000 : ℝ)*(sp3) + (260782591/6250000000000 : ℝ)*(sp4) + (275787553/12500000000000 : ℝ)*(sp7) + (191698277891583/25000000000000 : ℝ)*(f.failure) + (1565110532652261/100000000000000 : ℝ)*(f.sum) + (61157637143333/16482500000000000000000000000 : ℝ)*base65 + (9981544683430293523/1648250000000000000000000000000000 : ℝ)*base68 + (2421891289706793523/1648250000000000000000000000000000 : ℝ)*base70 + (2387789303781293523/1648250000000000000000000000000000 : ℝ)*base72 + (914739453071/8241250000000000000000000000 : ℝ)*base74 + (7466000300102043523/1648250000000000000000000000000000 : ℝ)*base76 + (1830011020953206477/1648250000000000000000000000000000 : ℝ)*base77 + (11063251201553793523/1648250000000000000000000000000000 : ℝ)*base80 + (14198731151439/8241250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (21689549/2500000000000000000000 : ℝ)*base89 + (21689549/2500000000000000000000 : ℝ)*base91 + (21689549/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7275336302238189049210289829/824125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15045957/100000000000000 : ℝ)*(base1) + (424507937/25000000000000 : ℝ)*(base19) + (1633151827/100000000000000 : ℝ)*(base23) + (122612863/50000000000000 : ℝ)*(upper3) + (190494237/100000000000000 : ℝ)*(upper5) + (149662428860357/12500000000000 : ℝ)*(major0) + (149662428860357/12500000000000 : ℝ)*(major1) + (149662428860357/12500000000000 : ℝ)*(major2) + (1149756143/12500000000000 : ℝ)*(sp1) + (198798901/2500000000000 : ℝ)*(sp2) + (803594814995997/50000000000000 : ℝ)*(sp4) + (200897339858143/12500000000000 : ℝ)*(sp5) + (160718002983817/10000000000000 : ℝ)*(sp6) + (393704468754313/50000000000000 : ℝ)*(sp7) + (787408952554583/100000000000000 : ℝ)*(f.failure) + (1607189614946037/100000000000000 : ℝ)*(f.sum) + (5331088481749/4120625000000000000000000000 : ℝ)*base65 + (6787376801031540019/1648250000000000000000000000000000 : ℝ)*base67 + (10767524143475540019/1648250000000000000000000000000000 : ℝ)*base69 + (19361007762821040019/1648250000000000000000000000000000 : ℝ)*base71 + (9194738341051/4120625000000000000000000000 : ℝ)*base74 + (25414734392590540019/1648250000000000000000000000000000 : ℝ)*base75 + (6532441284563040019/1648250000000000000000000000000000 : ℝ)*base77 + (9263932458593040019/1648250000000000000000000000000000 : ℝ)*base79 + (7764552948117/8241250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (91521451/10000000000000000000000 : ℝ)*base90 + (91521451/10000000000000000000000 : ℝ)*base92 + (91521451/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1273_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3973/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1273_s2_0 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-523067157/2500000000 : ℝ)*x 0 + (1371859823/2500000000 : ℝ)*x 1 + (5179285109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523067157/2500000000 : ℝ)^8467 ≤ (1587700351889/12500000000000 : ℝ)^6419 := by
    have hnat : (523067157 : ℕ)^8467*12500000000000^6419 ≤ 1587700351889^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523067157 2500000000 1587700351889 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371859823/2500000000 : ℝ)^8467 ≤ (9062434973209/20000000000000 : ℝ)^6419 := by
    have hnat : (1371859823 : ℕ)^8467*20000000000000^6419 ≤ 9062434973209^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371859823 2500000000 9062434973209 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179285109/10000000000 : ℝ)^8467 ≤ (20993111151407/50000000000000 : ℝ)^6419 := by
    have hnat : (5179285109 : ℕ)^8467*50000000000000^6419 ≤ 20993111151407^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179285109 10000000000 20993111151407 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523067157/2500000000 : ℝ), (1371859823/2500000000 : ℝ), (5179285109/10000000000 : ℝ)] ![(1587700351889/12500000000000 : ℝ), (9062434973209/20000000000000 : ℝ), (20993111151407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523067157/2500000000 : ℝ)|^8467 ≤ (1587700351889/12500000000000 : ℝ)^6419
        have hw : |(-523067157/2500000000 : ℝ)|=(523067157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371859823/2500000000 : ℝ)|^8467 ≤ (9062434973209/20000000000000 : ℝ)^6419
        have hw : |(1371859823/2500000000 : ℝ)|=(1371859823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179285109/10000000000 : ℝ)|^8467 ≤ (20993111151407/50000000000000 : ℝ)^6419
        have hw : |(5179285109/10000000000 : ℝ)|=(5179285109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_1 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368400701/10000000000 : ℝ)*x 0 + (-450343193/2000000000 : ℝ)*x 1 + (5179285413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368400701/10000000000 : ℝ)^8467 ≤ (44020116528019/100000000000000 : ℝ)^6419 := by
    have hnat : (5368400701 : ℕ)^8467*100000000000000^6419 ≤ 44020116528019^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368400701 10000000000 44020116528019 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450343193/2000000000 : ℝ)^8467 ≤ (6996828951001/50000000000000 : ℝ)^6419 := by
    have hnat : (450343193 : ℕ)^8467*50000000000000^6419 ≤ 6996828951001^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450343193 2000000000 6996828951001 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179285413/10000000000 : ℝ)^8467 ≤ (41986225553483/100000000000000 : ℝ)^6419 := by
    have hnat : (5179285413 : ℕ)^8467*100000000000000^6419 ≤ 41986225553483^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179285413 10000000000 41986225553483 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368400701/10000000000 : ℝ), (-450343193/2000000000 : ℝ), (5179285413/10000000000 : ℝ)] ![(44020116528019/100000000000000 : ℝ), (6996828951001/50000000000000 : ℝ), (41986225553483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368400701/10000000000 : ℝ)|^8467 ≤ (44020116528019/100000000000000 : ℝ)^6419
        have hw : |(5368400701/10000000000 : ℝ)|=(5368400701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450343193/2000000000 : ℝ)|^8467 ≤ (6996828951001/50000000000000 : ℝ)^6419
        have hw : |(-450343193/2000000000 : ℝ)|=(450343193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179285413/10000000000 : ℝ)|^8467 ≤ (41986225553483/100000000000000 : ℝ)^6419
        have hw : |(5179285413/10000000000 : ℝ)|=(5179285413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_2 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214736027/400000000 : ℝ)*x 0 + (5179285377/10000000000 : ℝ)*x 1 + (-1125858023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214736027/400000000 : ℝ)^8467 ≤ (22010058123401/50000000000000 : ℝ)^6419 := by
    have hnat : (214736027 : ℕ)^8467*50000000000000^6419 ≤ 22010058123401^6419*400000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214736027 400000000 22010058123401 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179285377/10000000000 : ℝ)^8467 ≤ (8397245033707/20000000000000 : ℝ)^6419 := by
    have hnat : (5179285377 : ℕ)^8467*20000000000000^6419 ≤ 8397245033707^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179285377 10000000000 8397245033707 20000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125858023/5000000000 : ℝ)^8467 ≤ (13993658565997/100000000000000 : ℝ)^6419 := by
    have hnat : (1125858023 : ℕ)^8467*100000000000000^6419 ≤ 13993658565997^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125858023 5000000000 13993658565997 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214736027/400000000 : ℝ), (5179285377/10000000000 : ℝ), (-1125858023/5000000000 : ℝ)] ![(22010058123401/50000000000000 : ℝ), (8397245033707/20000000000000 : ℝ), (13993658565997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214736027/400000000 : ℝ)|^8467 ≤ (22010058123401/50000000000000 : ℝ)^6419
        have hw : |(214736027/400000000 : ℝ)|=(214736027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179285377/10000000000 : ℝ)|^8467 ≤ (8397245033707/20000000000000 : ℝ)^6419
        have hw : |(5179285377/10000000000 : ℝ)|=(5179285377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125858023/5000000000 : ℝ)|^8467 ≤ (13993658565997/100000000000000 : ℝ)^6419
        have hw : |(-1125858023/5000000000 : ℝ)|=(1125858023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_3 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2169112507/5000000000 : ℝ)*x 0 + (2017349393/5000000000 : ℝ)*x 1 + (2331837579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169112507/5000000000 : ℝ)^8467 ≤ (33234983808739/100000000000000 : ℝ)^6419 := by
    have hnat : (2169112507 : ℕ)^8467*100000000000000^6419 ≤ 33234983808739^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169112507 5000000000 33234983808739 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017349393/5000000000 : ℝ)^8467 ≤ (15101290101319/50000000000000 : ℝ)^6419 := by
    have hnat : (2017349393 : ℕ)^8467*50000000000000^6419 ≤ 15101290101319^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017349393 5000000000 15101290101319 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2331837579/5000000000 : ℝ)^8467 ≤ (36562435967679/100000000000000 : ℝ)^6419 := by
    have hnat : (2331837579 : ℕ)^8467*100000000000000^6419 ≤ 36562435967679^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331837579 5000000000 36562435967679 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169112507/5000000000 : ℝ), (2017349393/5000000000 : ℝ), (2331837579/5000000000 : ℝ)] ![(33234983808739/100000000000000 : ℝ), (15101290101319/50000000000000 : ℝ), (36562435967679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169112507/5000000000 : ℝ)|^8467 ≤ (33234983808739/100000000000000 : ℝ)^6419
        have hw : |(2169112507/5000000000 : ℝ)|=(2169112507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017349393/5000000000 : ℝ)|^8467 ≤ (15101290101319/50000000000000 : ℝ)^6419
        have hw : |(2017349393/5000000000 : ℝ)|=(2017349393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2331837579/5000000000 : ℝ)|^8467 ≤ (36562435967679/100000000000000 : ℝ)^6419
        have hw : |(2331837579/5000000000 : ℝ)|=(2331837579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_4 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13077129/62500000 : ℝ)*x 0 + (647652869/1250000000 : ℝ)*x 1 + (5485483687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13077129/62500000 : ℝ)^8467 ≤ (6351089731381/50000000000000 : ℝ)^6419 := by
    have hnat : (13077129 : ℕ)^8467*50000000000000^6419 ≤ 6351089731381^6419*62500000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13077129 62500000 6351089731381 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647652869/1250000000 : ℝ)^8467 ≤ (10501736218899/25000000000000 : ℝ)^6419 := by
    have hnat : (647652869 : ℕ)^8467*25000000000000^6419 ≤ 10501736218899^6419*1250000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647652869 1250000000 10501736218899 25000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485483687/10000000000 : ℝ)^8467 ≤ (45290875640671/100000000000000 : ℝ)^6419 := by
    have hnat : (5485483687 : ℕ)^8467*100000000000000^6419 ≤ 45290875640671^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485483687 10000000000 45290875640671 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13077129/62500000 : ℝ), (647652869/1250000000 : ℝ), (5485483687/10000000000 : ℝ)] ![(6351089731381/50000000000000 : ℝ), (10501736218899/25000000000000 : ℝ), (45290875640671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13077129/62500000 : ℝ)|^8467 ≤ (6351089731381/50000000000000 : ℝ)^6419
        have hw : |(-13077129/62500000 : ℝ)|=(13077129/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647652869/1250000000 : ℝ)|^8467 ≤ (10501736218899/25000000000000 : ℝ)^6419
        have hw : |(647652869/1250000000 : ℝ)|=(647652869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485483687/10000000000 : ℝ)|^8467 ≤ (45290875640671/100000000000000 : ℝ)^6419
        have hw : |(5485483687/10000000000 : ℝ)|=(5485483687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_5 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322387857/2500000000 : ℝ)*x 0 + (-972758697/5000000000 : ℝ)*x 1 + (5485483727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322387857/2500000000 : ℝ)^8467 ≤ (43169284278513/100000000000000 : ℝ)^6419 := by
    have hnat : (1322387857 : ℕ)^8467*100000000000000^6419 ≤ 43169284278513^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322387857 2500000000 43169284278513 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972758697/5000000000 : ℝ)^8467 ≤ (11539839623011/100000000000000 : ℝ)^6419 := by
    have hnat : (972758697 : ℕ)^8467*100000000000000^6419 ≤ 11539839623011^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972758697 5000000000 11539839623011 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485483727/10000000000 : ℝ)^8467 ≤ (45290876076301/100000000000000 : ℝ)^6419 := by
    have hnat : (5485483727 : ℕ)^8467*100000000000000^6419 ≤ 45290876076301^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485483727 10000000000 45290876076301 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322387857/2500000000 : ℝ), (-972758697/5000000000 : ℝ), (5485483727/10000000000 : ℝ)] ![(43169284278513/100000000000000 : ℝ), (11539839623011/100000000000000 : ℝ), (45290876076301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322387857/2500000000 : ℝ)|^8467 ≤ (43169284278513/100000000000000 : ℝ)^6419
        have hw : |(1322387857/2500000000 : ℝ)|=(1322387857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972758697/5000000000 : ℝ)|^8467 ≤ (11539839623011/100000000000000 : ℝ)^6419
        have hw : |(-972758697/5000000000 : ℝ)|=(972758697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485483727/10000000000 : ℝ)|^8467 ≤ (45290876076301/100000000000000 : ℝ)^6419
        have hw : |(5485483727/10000000000 : ℝ)|=(5485483727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_6 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289551521/10000000000 : ℝ)*x 0 + (5485483853/10000000000 : ℝ)*x 1 + (-486379273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289551521/10000000000 : ℝ)^8467 ≤ (43169285279667/100000000000000 : ℝ)^6419 := by
    have hnat : (5289551521 : ℕ)^8467*100000000000000^6419 ≤ 43169285279667^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289551521 10000000000 43169285279667 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485483853/10000000000 : ℝ)^8467 ≤ (5661359681067/12500000000000 : ℝ)^6419 := by
    have hnat : (5485483853 : ℕ)^8467*12500000000000^6419 ≤ 5661359681067^6419*10000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485483853 10000000000 5661359681067 12500000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486379273/2500000000 : ℝ)^8467 ≤ (5769918630087/50000000000000 : ℝ)^6419 := by
    have hnat : (486379273 : ℕ)^8467*50000000000000^6419 ≤ 5769918630087^6419*2500000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486379273 2500000000 5769918630087 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289551521/10000000000 : ℝ), (5485483853/10000000000 : ℝ), (-486379273/2500000000 : ℝ)] ![(43169285279667/100000000000000 : ℝ), (5661359681067/12500000000000 : ℝ), (5769918630087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289551521/10000000000 : ℝ)|^8467 ≤ (43169285279667/100000000000000 : ℝ)^6419
        have hw : |(5289551521/10000000000 : ℝ)|=(5289551521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485483853/10000000000 : ℝ)|^8467 ≤ (5661359681067/12500000000000 : ℝ)^6419
        have hw : |(5485483853/10000000000 : ℝ)|=(5485483853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486379273/2500000000 : ℝ)|^8467 ≤ (5769918630087/50000000000000 : ℝ)^6419
        have hw : |(-486379273/2500000000 : ℝ)|=(486379273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1273_s2_7 (p : ℝ) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2169185823/5000000000 : ℝ)*x 0 + (931944083/2000000000 : ℝ)*x 1 + (50483617/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169185823/5000000000 : ℝ)^8467 ≤ (16618232782347/50000000000000 : ℝ)^6419 := by
    have hnat : (2169185823 : ℕ)^8467*50000000000000^6419 ≤ 16618232782347^6419*5000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169185823 5000000000 16618232782347 50000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931944083/2000000000 : ℝ)^8467 ≤ (36521544893889/100000000000000 : ℝ)^6419 := by
    have hnat : (931944083 : ℕ)^8467*100000000000000^6419 ≤ 36521544893889^6419*2000000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931944083 2000000000 36521544893889 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50483617/125000000 : ℝ)^8467 ≤ (30241989526547/100000000000000 : ℝ)^6419 := by
    have hnat : (50483617 : ℕ)^8467*100000000000000^6419 ≤ 30241989526547^6419*125000000^8467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50483617 125000000 30241989526547 100000000000000 8467 6419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8467/2048 : ℝ)) 8467 6419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169185823/5000000000 : ℝ), (931944083/2000000000 : ℝ), (50483617/125000000 : ℝ)] ![(16618232782347/50000000000000 : ℝ), (36521544893889/100000000000000 : ℝ), (30241989526547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169185823/5000000000 : ℝ)|^8467 ≤ (16618232782347/50000000000000 : ℝ)^6419
        have hw : |(2169185823/5000000000 : ℝ)|=(2169185823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(931944083/2000000000 : ℝ)|^8467 ≤ (36521544893889/100000000000000 : ℝ)^6419
        have hw : |(931944083/2000000000 : ℝ)|=(931944083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50483617/125000000 : ℝ)|^8467 ≤ (30241989526547/100000000000000 : ℝ)^6419
        have hw : |(50483617/125000000 : ℝ)|=(50483617/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1273_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9627/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16141/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6357/100000 : ℝ) ^ (4233/1024 : ℝ) ≤ (1129528207739807/100000000000000000000 : ℝ) := by
    have hpowers : (6357/100000 : ℝ)^4233 ≤ (1129528207739807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6357 : ℕ)^4233*100000000000000000000^1024 ≤ 1129528207739807^1024*100000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6357 100000 1129528207739807 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6357/100000 : ℝ)) (X := (1129528207739807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3973/20000 : ℝ) ^ (4233/1024 : ℝ) ≤ (125442934601050979/100000000000000000000 : ℝ) := by
    have hpowers : (3973/20000 : ℝ)^4233 ≤ (125442934601050979/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3973 : ℕ)^4233*100000000000000000000^1024 ≤ 125442934601050979^1024*20000^4233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3973 20000 125442934601050979 100000000000000000000 4233 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3973/20000 : ℝ)) (X := (125442934601050979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001129528207739807/50000000000000000000 : ℝ) ≤ (5000027324048683/5000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50001129528207739807/50000000000000000000 : ℝ)^1024 ≤ (5000027324048683/5000000000000000 : ℝ)^4233 := by
      have hnat : (50001129528207739807 : ℕ)^1024*5000000000000000^4233 ≤ 5000027324048683^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001129528207739807 50000000000000000000 5000027324048683 5000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027324048683/5000000000000000 : ℝ)) (X := (50001129528207739807/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50063286231404395393/50000000000000000000 : ℝ) ≤ (10003060431496763/10000000000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50063286231404395393/50000000000000000000 : ℝ)^1024 ≤ (10003060431496763/10000000000000000 : ℝ)^4233 := by
      have hnat : (50063286231404395393 : ℕ)^1024*10000000000000000^4233 ≤ 10003060431496763^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063286231404395393 50000000000000000000 10003060431496763 10000000000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003060431496763/10000000000000000 : ℝ)) (X := (50063286231404395393/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50125442934601050979/50000000000000000000 : ℝ) ≤ (62537913843101/62500000000000 : ℝ) ^ (4233/1024 : ℝ) := by
    have hpowers : (50125442934601050979/50000000000000000000 : ℝ)^1024 ≤ (62537913843101/62500000000000 : ℝ)^4233 := by
      have hnat : (50125442934601050979 : ℕ)^1024*62500000000000^4233 ≤ 62537913843101^4233*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50125442934601050979 50000000000000000000 62537913843101 62500000000000 1024 4233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62537913843101/62500000000000 : ℝ)) (X := (50125442934601050979/50000000000000000000 : ℝ)) (by norm_num) 4233 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1129528207739807/100000000000000000000 : ℝ) ≤ ((13504252265635928647/13508000000000000000 : ℝ)+2*(3005783399397/1350800000000000 : ℝ)*(6357/100000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (13504252265635928647/13508000000000000000 : ℝ)+2*(3005783399397/1350800000000000 : ℝ)*(6357/100000 : ℝ)=(5000027324048683/5000000000000000 : ℝ) by norm_num, show 1+2*(1129528207739807/100000000000000000000 : ℝ)=(50001129528207739807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(125442934601050979/100000000000000000000 : ℝ)+(1129528207739807/100000000000000000000 : ℝ) ≤ ((13504252265635928647/13508000000000000000 : ℝ)+(3005783399397/1350800000000000 : ℝ)*((3973/20000 : ℝ)+(6357/100000 : ℝ)))^(4233/1024 : ℝ) := by
    rw [show (13504252265635928647/13508000000000000000 : ℝ)+(3005783399397/1350800000000000 : ℝ)*((3973/20000 : ℝ)+(6357/100000 : ℝ))=(10003060431496763/10000000000000000 : ℝ) by norm_num, show 1+(125442934601050979/100000000000000000000 : ℝ)+(1129528207739807/100000000000000000000 : ℝ)=(50063286231404395393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(125442934601050979/100000000000000000000 : ℝ) ≤ ((13504252265635928647/13508000000000000000 : ℝ)+2*(3005783399397/1350800000000000 : ℝ)*(3973/20000 : ℝ))^(4233/1024 : ℝ) := by
    rw [show (13504252265635928647/13508000000000000000 : ℝ)+2*(3005783399397/1350800000000000 : ℝ)*(3973/20000 : ℝ)=(62537913843101/62500000000000 : ℝ) by norm_num, show 1+2*(125442934601050979/100000000000000000000 : ℝ)=(50125442934601050979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13504252265635928647/13508000000000000000 : ℝ)*(X 1 0+X 2 0)+(3005783399397/1350800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (6357/100000 : ℝ)) (hi := (3973/20000 : ℝ)) (c := (13504252265635928647/13508000000000000000 : ℝ)) (alpha := (3005783399397/1350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13504252265635928647/13508000000000000000 : ℝ)*(X 0 1+X 2 1)+(3005783399397/1350800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (6357/100000 : ℝ)) (hi := (3973/20000 : ℝ)) (c := (13504252265635928647/13508000000000000000 : ℝ)) (alpha := (3005783399397/1350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13504252265635928647/13508000000000000000 : ℝ)*(X 0 2+X 1 2)+(3005783399397/1350800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4233/1024 : ℝ)) (lo := (6357/100000 : ℝ)) (hi := (3973/20000 : ℝ)) (c := (13504252265635928647/13508000000000000000 : ℝ)) (alpha := (3005783399397/1350800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-523067157/2500000000 : ℝ)*X 0 0+(1371859823/2500000000 : ℝ)*X 0 1+(5179285109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368400701/10000000000 : ℝ)*X 1 0+(-450343193/2000000000 : ℝ)*X 1 1+(5179285413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214736027/400000000 : ℝ)*X 2 0+(5179285377/10000000000 : ℝ)*X 2 1+(-1125858023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169112507/5000000000 : ℝ)*X 0 0+(2017349393/5000000000 : ℝ)*X 0 1+(2331837579/5000000000 : ℝ)*X 0 2+(2169112507/5000000000 : ℝ)*X 1 0+(2017349393/5000000000 : ℝ)*X 1 1+(2331837579/5000000000 : ℝ)*X 1 2+(2169112507/5000000000 : ℝ)*X 2 0+(2017349393/5000000000 : ℝ)*X 2 1+(2331837579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13077129/62500000 : ℝ)*X 0 0+(647652869/1250000000 : ℝ)*X 0 1+(5485483687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322387857/2500000000 : ℝ)*X 1 0+(-972758697/5000000000 : ℝ)*X 1 1+(5485483727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289551521/10000000000 : ℝ)*X 2 0+(5485483853/10000000000 : ℝ)*X 2 1+(-486379273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169185823/5000000000 : ℝ)*X 0 0+(931944083/2000000000 : ℝ)*X 0 1+(50483617/125000000 : ℝ)*X 0 2+(2169185823/5000000000 : ℝ)*X 1 0+(931944083/2000000000 : ℝ)*X 1 1+(50483617/125000000 : ℝ)*X 1 2+(2169185823/5000000000 : ℝ)*X 2 0+(931944083/2000000000 : ℝ)*X 2 1+(50483617/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1273_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202362199193561005696875309/30700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1139474981/100000000000000 : ℝ)*(base19) + (271644599/25000000000000 : ℝ)*(base23) + (1995959/10000000000000 : ℝ)*(lower2) + (177681021/100000000000000 : ℝ)*(upper3) + (8519923/10000000000000 : ℝ)*(upper5) + (1208764983381261/50000000000000 : ℝ)*(major0) + (1208764983381261/50000000000000 : ℝ)*(major1) + (1208764983381261/50000000000000 : ℝ)*(major2) + (324514571341237/10000000000000 : ℝ)*(sp0) + (1622579966302891/50000000000000 : ℝ)*(sp1) + (101411249546949/3125000000000 : ℝ)*(sp2) + (317978252774201/20000000000000 : ℝ)*(sp3) + (15358668393/100000000000000 : ℝ)*(sp4) + (3688926591/50000000000000 : ℝ)*(sp7) + (1589898641724187/100000000000000 : ℝ)*(f.failure) + (811290268020191/25000000000000 : ℝ)*(f.sum) + (211120491753123/33770000000000000000000000000 : ℝ)*base66 + (5074264700034653867/675400000000000000000000000000000 : ℝ)*base67 + (2735467970611653867/675400000000000000000000000000000 : ℝ)*base69 + (1761689138340546133/675400000000000000000000000000000 : ℝ)*base72 + (85142905470517/33770000000000000000000000000 : ℝ)*base73 + (5146203823378653867/675400000000000000000000000000000 : ℝ)*base75 + (8339980598577746133/675400000000000000000000000000000 : ℝ)*base78 + (970619022210653867/675400000000000000000000000000000 : ℝ)*base79 + (148210421799477/33770000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13969761/10000000000000000000000 : ℝ)*base89 + (13969761/10000000000000000000000 : ℝ)*base91 + (13969761/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69559280363921476117510347/30700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169154497/20000000000000 : ℝ)*(base19) + (562409019/50000000000000 : ℝ)*(base23) + (33654857/50000000000000 : ℝ)*(upper2) + (136024759/100000000000000 : ℝ)*(upper3) + (37873081/100000000000000 : ℝ)*(upper5) + (1224219713844679/50000000000000 : ℝ)*(major0) + (1224219713844679/50000000000000 : ℝ)*(major1) + (1224219713844679/50000000000000 : ℝ)*(major2) + (1691369313/20000000000000 : ℝ)*(sp1) + (14763459437/100000000000000 : ℝ)*(sp2) + (1643326201269607/50000000000000 : ℝ)*(sp4) + (821660774980041/25000000000000 : ℝ)*(sp5) + (164331825713087/5000000000000 : ℝ)*(sp6) + (201278297164209/12500000000000 : ℝ)*(sp7) + (201278297164209/12500000000000 : ℝ)*(f.failure) + (1643326201269607/50000000000000 : ℝ)*(f.sum) + (112622252864477/33770000000000000000000000000 : ℝ)*base66 + (8770396715372950687/675400000000000000000000000000000 : ℝ)*base68 + (5081279739454950687/675400000000000000000000000000000 : ℝ)*base70 + (10054485269752350687/675400000000000000000000000000000 : ℝ)*base72 + (167690447728467/33770000000000000000000000000 : ℝ)*base74 + (306218999301950687/675400000000000000000000000000000 : ℝ)*base76 + (5980060650005550687/675400000000000000000000000000000 : ℝ)*base78 + (13035951091944350687/675400000000000000000000000000000 : ℝ)*base80 + (152712530773697/33770000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14513027/1250000000000000000000 : ℝ)*base89 + (14513027/1250000000000000000000 : ℝ)*base91 + (14513027/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1273_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1273_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1273_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1273_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1273_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1273_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4233/1024 : ℝ) ≤ p) (hpb : p ≤ (8467/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152055603/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16141/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1273_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
