-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:00.001101+00:00
-- url     : https://prove2.me/submissions/62a26ef7-8d12-4ddf-8f98-6a412a1f6c17

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
theorem support_rectangle_w1117_s0_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899748457/10000000000 : ℝ)*x 0 + (6060126381/10000000000 : ℝ)*x 1 + (955460479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899748457/10000000000 : ℝ)^4155 ≤ (2758876010539/25000000000000 : ℝ)^3131 := by
    have hnat : (1899748457 : ℕ)^4155*25000000000000^3131 ≤ 2758876010539^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899748457 10000000000 2758876010539 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6060126381/10000000000 : ℝ)^4155 ≤ (25722422734647/50000000000000 : ℝ)^3131 := by
    have hnat : (6060126381 : ℕ)^4155*50000000000000^3131 ≤ 25722422734647^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6060126381 10000000000 25722422734647 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955460479/2000000000 : ℝ)^4155 ≤ (9379912618661/25000000000000 : ℝ)^3131 := by
    have hnat : (955460479 : ℕ)^4155*25000000000000^3131 ≤ 9379912618661^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955460479 2000000000 9379912618661 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899748457/10000000000 : ℝ), (6060126381/10000000000 : ℝ), (955460479/2000000000 : ℝ)] ![(2758876010539/25000000000000 : ℝ), (25722422734647/50000000000000 : ℝ), (9379912618661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899748457/10000000000 : ℝ)|^4155 ≤ (2758876010539/25000000000000 : ℝ)^3131
        have hw : |(-1899748457/10000000000 : ℝ)|=(1899748457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6060126381/10000000000 : ℝ)|^4155 ≤ (25722422734647/50000000000000 : ℝ)^3131
        have hw : |(6060126381/10000000000 : ℝ)|=(6060126381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955460479/2000000000 : ℝ)|^4155 ≤ (9379912618661/25000000000000 : ℝ)^3131
        have hw : |(955460479/2000000000 : ℝ)|=(955460479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5518201763/10000000000 : ℝ)*x 0 + (-2636660269/10000000000 : ℝ)*x 1 + (1194325609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518201763/10000000000 : ℝ)^4155 ≤ (5678870351037/12500000000000 : ℝ)^3131 := by
    have hnat : (5518201763 : ℕ)^4155*12500000000000^3131 ≤ 5678870351037^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518201763 10000000000 5678870351037 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636660269/10000000000 : ℝ)^4155 ≤ (681975450869/4000000000000 : ℝ)^3131 := by
    have hnat : (2636660269 : ℕ)^4155*4000000000000^3131 ≤ 681975450869^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636660269 10000000000 681975450869 4000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194325609/2500000000 : ℝ)^4155 ≤ (18759825450979/50000000000000 : ℝ)^3131 := by
    have hnat : (1194325609 : ℕ)^4155*50000000000000^3131 ≤ 18759825450979^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194325609 2500000000 18759825450979 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518201763/10000000000 : ℝ), (-2636660269/10000000000 : ℝ), (1194325609/2500000000 : ℝ)] ![(5678870351037/12500000000000 : ℝ), (681975450869/4000000000000 : ℝ), (18759825450979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518201763/10000000000 : ℝ)|^4155 ≤ (5678870351037/12500000000000 : ℝ)^3131
        have hw : |(5518201763/10000000000 : ℝ)|=(5518201763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2636660269/10000000000 : ℝ)|^4155 ≤ (681975450869/4000000000000 : ℝ)^3131
        have hw : |(-2636660269/10000000000 : ℝ)|=(2636660269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194325609/2500000000 : ℝ)|^4155 ≤ (18759825450979/50000000000000 : ℝ)^3131
        have hw : |(1194325609/2500000000 : ℝ)|=(1194325609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1379550479/2500000000 : ℝ)*x 0 + (4777302293/10000000000 : ℝ)*x 1 + (-329582531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379550479/2500000000 : ℝ)^4155 ≤ (22715482239951/50000000000000 : ℝ)^3131 := by
    have hnat : (1379550479 : ℕ)^4155*50000000000000^3131 ≤ 22715482239951^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379550479 2500000000 22715482239951 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4777302293/10000000000 : ℝ)^4155 ≤ (2344978088223/6250000000000 : ℝ)^3131 := by
    have hnat : (4777302293 : ℕ)^4155*6250000000000^3131 ≤ 2344978088223^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777302293 10000000000 2344978088223 6250000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329582531/1250000000 : ℝ)^4155 ≤ (8524693045761/50000000000000 : ℝ)^3131 := by
    have hnat : (329582531 : ℕ)^4155*50000000000000^3131 ≤ 8524693045761^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329582531 1250000000 8524693045761 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379550479/2500000000 : ℝ), (4777302293/10000000000 : ℝ), (-329582531/1250000000 : ℝ)] ![(22715482239951/50000000000000 : ℝ), (2344978088223/6250000000000 : ℝ), (8524693045761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379550479/2500000000 : ℝ)|^4155 ≤ (22715482239951/50000000000000 : ℝ)^3131
        have hw : |(1379550479/2500000000 : ℝ)|=(1379550479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4777302293/10000000000 : ℝ)|^4155 ≤ (2344978088223/6250000000000 : ℝ)^3131
        have hw : |(4777302293/10000000000 : ℝ)|=(4777302293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329582531/1250000000 : ℝ)|^4155 ≤ (8524693045761/50000000000000 : ℝ)^3131
        have hw : |(-329582531/1250000000 : ℝ)|=(329582531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262688781/625000000 : ℝ)*x 0 + (19514157/62500000 : ℝ)*x 1 + (5661901867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262688781/625000000 : ℝ)^4155 ≤ (31655306544117/100000000000000 : ℝ)^3131 := by
    have hnat : (262688781 : ℕ)^4155*100000000000000^3131 ≤ 31655306544117^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262688781 625000000 31655306544117 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19514157/62500000 : ℝ)^4155 ≤ (21337084479099/100000000000000 : ℝ)^3131 := by
    have hnat : (19514157 : ℕ)^4155*100000000000000^3131 ≤ 21337084479099^3131*62500000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19514157 62500000 21337084479099 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661901867/10000000000 : ℝ)^4155 ≤ (23503804487111/50000000000000 : ℝ)^3131 := by
    have hnat : (5661901867 : ℕ)^4155*50000000000000^3131 ≤ 23503804487111^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661901867 10000000000 23503804487111 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262688781/625000000 : ℝ), (19514157/62500000 : ℝ), (5661901867/10000000000 : ℝ)] ![(31655306544117/100000000000000 : ℝ), (21337084479099/100000000000000 : ℝ), (23503804487111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262688781/625000000 : ℝ)|^4155 ≤ (31655306544117/100000000000000 : ℝ)^3131
        have hw : |(262688781/625000000 : ℝ)|=(262688781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19514157/62500000 : ℝ)|^4155 ≤ (21337084479099/100000000000000 : ℝ)^3131
        have hw : |(19514157/62500000 : ℝ)|=(19514157/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661901867/10000000000 : ℝ)|^4155 ≤ (23503804487111/50000000000000 : ℝ)^3131
        have hw : |(5661901867/10000000000 : ℝ)|=(5661901867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1904969233/10000000000 : ℝ)*x 0 + (4810407967/10000000000 : ℝ)*x 1 + (753232253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1904969233/10000000000 : ℝ)^4155 ≤ (11075767780857/100000000000000 : ℝ)^3131 := by
    have hnat : (1904969233 : ℕ)^4155*100000000000000^3131 ≤ 11075767780857^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904969233 10000000000 11075767780857 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810407967/10000000000 : ℝ)^4155 ≤ (9466269354319/25000000000000 : ℝ)^3131 := by
    have hnat : (4810407967 : ℕ)^4155*25000000000000^3131 ≤ 9466269354319^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810407967 10000000000 9466269354319 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753232253/1250000000 : ℝ)^4155 ≤ (2042366191657/4000000000000 : ℝ)^3131 := by
    have hnat : (753232253 : ℕ)^4155*4000000000000^3131 ≤ 2042366191657^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753232253 1250000000 2042366191657 4000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1904969233/10000000000 : ℝ), (4810407967/10000000000 : ℝ), (753232253/1250000000 : ℝ)] ![(11075767780857/100000000000000 : ℝ), (9466269354319/25000000000000 : ℝ), (2042366191657/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1904969233/10000000000 : ℝ)|^4155 ≤ (11075767780857/100000000000000 : ℝ)^3131
        have hw : |(-1904969233/10000000000 : ℝ)|=(1904969233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810407967/10000000000 : ℝ)|^4155 ≤ (9466269354319/25000000000000 : ℝ)^3131
        have hw : |(4810407967/10000000000 : ℝ)|=(4810407967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753232253/1250000000 : ℝ)|^4155 ≤ (2042366191657/4000000000000 : ℝ)^3131
        have hw : |(753232253/1250000000 : ℝ)|=(753232253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2584876147/5000000000 : ℝ)*x 0 + (-694052711/5000000000 : ℝ)*x 1 + (6025861027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584876147/5000000000 : ℝ)^4155 ≤ (8332770422947/20000000000000 : ℝ)^3131 := by
    have hnat : (2584876147 : ℕ)^4155*20000000000000^3131 ≤ 8332770422947^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584876147 5000000000 8332770422947 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694052711/5000000000 : ℝ)^4155 ≤ (7276959308279/100000000000000 : ℝ)^3131 := by
    have hnat : (694052711 : ℕ)^4155*100000000000000^3131 ≤ 7276959308279^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694052711 5000000000 7276959308279 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6025861027/10000000000 : ℝ)^4155 ≤ (25529594279429/50000000000000 : ℝ)^3131 := by
    have hnat : (6025861027 : ℕ)^4155*50000000000000^3131 ≤ 25529594279429^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6025861027 10000000000 25529594279429 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584876147/5000000000 : ℝ), (-694052711/5000000000 : ℝ), (6025861027/10000000000 : ℝ)] ![(8332770422947/20000000000000 : ℝ), (7276959308279/100000000000000 : ℝ), (25529594279429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584876147/5000000000 : ℝ)|^4155 ≤ (8332770422947/20000000000000 : ℝ)^3131
        have hw : |(2584876147/5000000000 : ℝ)|=(2584876147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-694052711/5000000000 : ℝ)|^4155 ≤ (7276959308279/100000000000000 : ℝ)^3131
        have hw : |(-694052711/5000000000 : ℝ)|=(694052711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6025861027/10000000000 : ℝ)|^4155 ≤ (25529594279429/50000000000000 : ℝ)^3131
        have hw : |(6025861027/10000000000 : ℝ)|=(6025861027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646219513/1250000000 : ℝ)*x 0 + (1506464617/2500000000 : ℝ)*x 1 + (-694051851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646219513/1250000000 : ℝ)^4155 ≤ (8332778572479/20000000000000 : ℝ)^3131 := by
    have hnat : (646219513 : ℕ)^4155*20000000000000^3131 ≤ 8332778572479^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646219513 1250000000 8332778572479 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506464617/2500000000 : ℝ)^4155 ≤ (12764789946003/25000000000000 : ℝ)^3131 := by
    have hnat : (1506464617 : ℕ)^4155*25000000000000^3131 ≤ 12764789946003^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506464617 2500000000 12764789946003 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694051851/5000000000 : ℝ)^4155 ≤ (3638473671211/50000000000000 : ℝ)^3131 := by
    have hnat : (694051851 : ℕ)^4155*50000000000000^3131 ≤ 3638473671211^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694051851 5000000000 3638473671211 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646219513/1250000000 : ℝ), (1506464617/2500000000 : ℝ), (-694051851/5000000000 : ℝ)] ![(8332778572479/20000000000000 : ℝ), (12764789946003/25000000000000 : ℝ), (3638473671211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646219513/1250000000 : ℝ)|^4155 ≤ (8332778572479/20000000000000 : ℝ)^3131
        have hw : |(646219513/1250000000 : ℝ)|=(646219513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506464617/2500000000 : ℝ)|^4155 ≤ (12764789946003/25000000000000 : ℝ)^3131
        have hw : |(1506464617/2500000000 : ℝ)|=(1506464617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694051851/5000000000 : ℝ)|^4155 ≤ (3638473671211/50000000000000 : ℝ)^3131
        have hw : |(-694051851/5000000000 : ℝ)|=(694051851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s0_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213352637/10000000000 : ℝ)*x 0 + (1119273059/2000000000 : ℝ)*x 1 + (638020589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213352637/10000000000 : ℝ)^4155 ≤ (6351723089493/20000000000000 : ℝ)^3131 := by
    have hnat : (4213352637 : ℕ)^4155*20000000000000^3131 ≤ 6351723089493^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213352637 10000000000 6351723089493 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119273059/2000000000 : ℝ)^4155 ≤ (46286912266407/100000000000000 : ℝ)^3131 := by
    have hnat : (1119273059 : ℕ)^4155*100000000000000^3131 ≤ 46286912266407^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119273059 2000000000 46286912266407 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638020589/2000000000 : ℝ)^4155 ≤ (10977236137407/50000000000000 : ℝ)^3131 := by
    have hnat : (638020589 : ℕ)^4155*50000000000000^3131 ≤ 10977236137407^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638020589 2000000000 10977236137407 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213352637/10000000000 : ℝ), (1119273059/2000000000 : ℝ), (638020589/2000000000 : ℝ)] ![(6351723089493/20000000000000 : ℝ), (46286912266407/100000000000000 : ℝ), (10977236137407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213352637/10000000000 : ℝ)|^4155 ≤ (6351723089493/20000000000000 : ℝ)^3131
        have hw : |(4213352637/10000000000 : ℝ)|=(4213352637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119273059/2000000000 : ℝ)|^4155 ≤ (46286912266407/100000000000000 : ℝ)^3131
        have hw : |(1119273059/2000000000 : ℝ)|=(1119273059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638020589/2000000000 : ℝ)|^4155 ≤ (10977236137407/50000000000000 : ℝ)^3131
        have hw : |(638020589/2000000000 : ℝ)|=(638020589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (31/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27911/100000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8309/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8309 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8309*1^2048 ≤ 0^2048*1^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8309/2048 : ℝ) ≤ (1214719748617641543/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8309 ≤ (1214719748617641543/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8309*50000000000000000000^2048 ≤ 1214719748617641543^2048*5^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1214719748617641543 50000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1214719748617641543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8309 := by
      have hnat : (1 : ℕ)^2048*1^8309 ≤ 1^8309*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51214719748617641543/50000000000000000000 : ℝ) ≤ (10059340314056659/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (51214719748617641543/50000000000000000000 : ℝ)^2048 ≤ (10059340314056659/10000000000000000 : ℝ)^8309 := by
      have hnat : (51214719748617641543 : ℕ)^2048*10000000000000000^8309 ≤ 10059340314056659^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51214719748617641543 50000000000000000000 10059340314056659 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059340314056659/10000000000000000 : ℝ)) (X := (51214719748617641543/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26214719748617641543/25000000000000000000 : ℝ) ≤ (5059340314056659/5000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (26214719748617641543/25000000000000000000 : ℝ)^2048 ≤ (5059340314056659/5000000000000000 : ℝ)^8309 := by
      have hnat : (26214719748617641543 : ℕ)^2048*5000000000000000^8309 ≤ 5059340314056659^8309*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26214719748617641543 25000000000000000000 5059340314056659 5000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059340314056659/5000000000000000 : ℝ)) (X := (26214719748617641543/25000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59340314056659/4000000000000000 : ℝ)*(0 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59340314056659/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1214719748617641543/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59340314056659/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (1 : ℝ)+(59340314056659/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059340314056659/10000000000000000 : ℝ) by norm_num, show 1+(1214719748617641543/50000000000000000000 : ℝ)+(0 : ℝ)=(51214719748617641543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1214719748617641543/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59340314056659/4000000000000000 : ℝ)*(2/5 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(59340314056659/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059340314056659/5000000000000000 : ℝ) by norm_num, show 1+2*(1214719748617641543/50000000000000000000 : ℝ)=(26214719748617641543/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59340314056659/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59340314056659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59340314056659/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59340314056659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59340314056659/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59340314056659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1899748457/10000000000 : ℝ)*X 0 0+(6060126381/10000000000 : ℝ)*X 0 1+(955460479/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518201763/10000000000 : ℝ)*X 1 0+(-2636660269/10000000000 : ℝ)*X 1 1+(1194325609/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379550479/2500000000 : ℝ)*X 2 0+(4777302293/10000000000 : ℝ)*X 2 1+(-329582531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262688781/625000000 : ℝ)*X 0 0+(19514157/62500000 : ℝ)*X 0 1+(5661901867/10000000000 : ℝ)*X 0 2+(262688781/625000000 : ℝ)*X 1 0+(19514157/62500000 : ℝ)*X 1 1+(5661901867/10000000000 : ℝ)*X 1 2+(262688781/625000000 : ℝ)*X 2 0+(19514157/62500000 : ℝ)*X 2 1+(5661901867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1904969233/10000000000 : ℝ)*X 0 0+(4810407967/10000000000 : ℝ)*X 0 1+(753232253/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584876147/5000000000 : ℝ)*X 1 0+(-694052711/5000000000 : ℝ)*X 1 1+(6025861027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646219513/1250000000 : ℝ)*X 2 0+(1506464617/2500000000 : ℝ)*X 2 1+(-694051851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213352637/10000000000 : ℝ)*X 0 0+(1119273059/2000000000 : ℝ)*X 0 1+(638020589/2000000000 : ℝ)*X 0 2+(4213352637/10000000000 : ℝ)*X 1 0+(1119273059/2000000000 : ℝ)*X 1 1+(638020589/2000000000 : ℝ)*X 1 2+(4213352637/10000000000 : ℝ)*X 2 0+(1119273059/2000000000 : ℝ)*X 2 1+(638020589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106982536532517677803851/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29905741/50000000000000 : ℝ)*(base1) + (330985721/25000000000000 : ℝ)*(base19) + (624880309/50000000000000 : ℝ)*(base23) + (23949003/25000000000000 : ℝ)*(base24) + (9589341/3125000000000 : ℝ)*(upper3) + (58664920216321/10000000000000 : ℝ)*(major0) + (58664920216321/10000000000000 : ℝ)*(major1) + (58664920216321/10000000000000 : ℝ)*(major2) + (389767271227909/50000000000000 : ℝ)*(sp0) + (97442004472003/12500000000000 : ℝ)*(sp1) + (389768007081139/50000000000000 : ℝ)*(sp2) + (78751692316601/20000000000000 : ℝ)*(sp3) + (719268643/25000000000000 : ℝ)*(sp4) + (1172454397/50000000000000 : ℝ)*(sp7) + (393760866303281/100000000000000 : ℝ)*(f.failure) + (194884339929727/25000000000000 : ℝ)*(f.sum) + (16257552588461/20000000000000000000000000000 : ℝ)*base66 + (5025746051539/40000000000000000000000000000 : ℝ)*base67 + (153277409588461/40000000000000000000000000000 : ℝ)*base70 + (110404292268461/40000000000000000000000000000 : ℝ)*base72 + (9487343051539/20000000000000000000000000000 : ℝ)*base73 + (103675194628461/40000000000000000000000000000 : ℝ)*base76 + (65788065708461/40000000000000000000000000000 : ℝ)*base78 + (41888400828461/40000000000000000000000000000 : ℝ)*base80 + (65361543888461/20000000000000000000000000000 : ℝ)*base82 + (17901239/5000000000000000000000 : ℝ)*base90 + (17901239/5000000000000000000000 : ℝ)*base92 + (17901239/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317667452732613508340367/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297368063/100000000000000 : ℝ)*(base13) + (490052019/50000000000000 : ℝ)*(base23) + (335720887/100000000000000 : ℝ)*(base39) + (43803687/100000000000000 : ℝ)*(base45) + (21271481/25000000000000 : ℝ)*(upper3) + (243231679/100000000000000 : ℝ)*(upper5) + (619159694763929/100000000000000 : ℝ)*(major0) + (619159694763929/100000000000000 : ℝ)*(major1) + (619159359043041/100000000000000 : ℝ)*(major2) + (353685517/50000000000000 : ℝ)*(sp2) + (822736635111343/100000000000000 : ℝ)*(sp4) + (822736932479407/100000000000000 : ℝ)*(sp5) + (411367790362611/50000000000000 : ℝ)*(sp6) + (207791007719203/50000000000000 : ℝ)*(sp7) + (207791007719203/50000000000000 : ℝ)*(f.failure) + (411368634100147/50000000000000 : ℝ)*(f.sum) + (26028845208677/40000000000000000000000000000 : ℝ)*base66 + (1803463113260019/400000000000000000000000000000 : ℝ)*base67 + (2753210574653211/400000000000000000000000000000 : ℝ)*base69 + (1711704381660019/400000000000000000000000000000 : ℝ)*base71 + (30093177728677/40000000000000000000000000000 : ℝ)*base74 + (1644648671853211/400000000000000000000000000000 : ℝ)*base75 + (1090226193853211/400000000000000000000000000000 : ℝ)*base77 + (3532527084253211/400000000000000000000000000000 : ℝ)*base79 + (1070023856653211/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10665557/2500000000000000000000 : ℝ)*base90 + (10665557/2500000000000000000000 : ℝ)*base92 + (14334443/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1117_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (31/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27911/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s1_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-421244081/2000000000 : ℝ)*x 0 + (5708239283/10000000000 : ℝ)*x 1 + (4996995181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421244081/2000000000 : ℝ)^4155 ≤ (12654772592687/100000000000000 : ℝ)^3131 := by
    have hnat : (421244081 : ℕ)^4155*100000000000000^3131 ≤ 12654772592687^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421244081 2000000000 12654772592687 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5708239283/10000000000 : ℝ)^4155 ≤ (1900753042649/4000000000000 : ℝ)^3131 := by
    have hnat : (5708239283 : ℕ)^4155*4000000000000^3131 ≤ 1900753042649^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708239283 10000000000 1900753042649 4000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996995181/10000000000 : ℝ)^4155 ≤ (622287520631/1562500000000 : ℝ)^3131 := by
    have hnat : (4996995181 : ℕ)^4155*1562500000000^3131 ≤ 622287520631^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996995181 10000000000 622287520631 1562500000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421244081/2000000000 : ℝ), (5708239283/10000000000 : ℝ), (4996995181/10000000000 : ℝ)] ![(12654772592687/100000000000000 : ℝ), (1900753042649/4000000000000 : ℝ), (622287520631/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421244081/2000000000 : ℝ)|^4155 ≤ (12654772592687/100000000000000 : ℝ)^3131
        have hw : |(-421244081/2000000000 : ℝ)|=(421244081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5708239283/10000000000 : ℝ)|^4155 ≤ (1900753042649/4000000000000 : ℝ)^3131
        have hw : |(5708239283/10000000000 : ℝ)|=(5708239283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4996995181/10000000000 : ℝ)|^4155 ≤ (622287520631/1562500000000 : ℝ)^3131
        have hw : |(4996995181/10000000000 : ℝ)|=(4996995181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420496261/10000000000 : ℝ)*x 0 + (-498107897/2000000000 : ℝ)*x 1 + (1249248757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420496261/10000000000 : ℝ)^4155 ≤ (4436658203651/10000000000000 : ℝ)^3131 := by
    have hnat : (5420496261 : ℕ)^4155*10000000000000^3131 ≤ 4436658203651^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420496261 10000000000 4436658203651 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498107897/2000000000 : ℝ)^4155 ≤ (15807018242829/100000000000000 : ℝ)^3131 := by
    have hnat : (498107897 : ℕ)^4155*100000000000000^3131 ≤ 15807018242829^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498107897 2000000000 15807018242829 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249248757/2500000000 : ℝ)^4155 ≤ (796527994043/2000000000000 : ℝ)^3131 := by
    have hnat : (1249248757 : ℕ)^4155*2000000000000^3131 ≤ 796527994043^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249248757 2500000000 796527994043 2000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420496261/10000000000 : ℝ), (-498107897/2000000000 : ℝ), (1249248757/2500000000 : ℝ)] ![(4436658203651/10000000000000 : ℝ), (15807018242829/100000000000000 : ℝ), (796527994043/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420496261/10000000000 : ℝ)|^4155 ≤ (4436658203651/10000000000000 : ℝ)^3131
        have hw : |(5420496261/10000000000 : ℝ)|=(5420496261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498107897/2000000000 : ℝ)|^4155 ≤ (15807018242829/100000000000000 : ℝ)^3131
        have hw : |(-498107897/2000000000 : ℝ)|=(498107897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249248757/2500000000 : ℝ)|^4155 ≤ (796527994043/2000000000000 : ℝ)^3131
        have hw : |(1249248757/2500000000 : ℝ)|=(1249248757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54204977/100000000 : ℝ)*x 0 + (2498496847/5000000000 : ℝ)*x 1 + (-498107861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54204977/100000000 : ℝ)^4155 ≤ (693228088543/1562500000000 : ℝ)^3131 := by
    have hnat : (54204977 : ℕ)^4155*1562500000000^3131 ≤ 693228088543^3131*100000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54204977 100000000 693228088543 1562500000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498496847/5000000000 : ℝ)^4155 ≤ (9956596398209/25000000000000 : ℝ)^3131 := by
    have hnat : (2498496847 : ℕ)^4155*25000000000000^3131 ≤ 9956596398209^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498496847 5000000000 9956596398209 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498107861/2000000000 : ℝ)^4155 ≤ (15807016726767/100000000000000 : ℝ)^3131 := by
    have hnat : (498107861 : ℕ)^4155*100000000000000^3131 ≤ 15807016726767^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498107861 2000000000 15807016726767 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54204977/100000000 : ℝ), (2498496847/5000000000 : ℝ), (-498107861/2000000000 : ℝ)] ![(693228088543/1562500000000 : ℝ), (9956596398209/25000000000000 : ℝ), (15807016726767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54204977/100000000 : ℝ)|^4155 ≤ (693228088543/1562500000000 : ℝ)^3131
        have hw : |(54204977/100000000 : ℝ)|=(54204977/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498496847/5000000000 : ℝ)|^4155 ≤ (9956596398209/25000000000000 : ℝ)^3131
        have hw : |(2498496847/5000000000 : ℝ)|=(2498496847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-498107861/2000000000 : ℝ)|^4155 ≤ (15807016726767/100000000000000 : ℝ)^3131
        have hw : |(-498107861/2000000000 : ℝ)|=(498107861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079887227/2500000000 : ℝ)*x 0 + (734465099/2000000000 : ℝ)*x 1 + (5080390251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079887227/2500000000 : ℝ)^4155 ≤ (8206307389581/25000000000000 : ℝ)^3131 := by
    have hnat : (1079887227 : ℕ)^4155*25000000000000^3131 ≤ 8206307389581^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079887227 2500000000 8206307389581 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734465099/2000000000 : ℝ)^4155 ≤ (26463926422637/100000000000000 : ℝ)^3131 := by
    have hnat : (734465099 : ℕ)^4155*100000000000000^3131 ≤ 26463926422637^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734465099 2000000000 26463926422637 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080390251/10000000000 : ℝ)^4155 ≤ (5088855500697/12500000000000 : ℝ)^3131 := by
    have hnat : (5080390251 : ℕ)^4155*12500000000000^3131 ≤ 5088855500697^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080390251 10000000000 5088855500697 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079887227/2500000000 : ℝ), (734465099/2000000000 : ℝ), (5080390251/10000000000 : ℝ)] ![(8206307389581/25000000000000 : ℝ), (26463926422637/100000000000000 : ℝ), (5088855500697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079887227/2500000000 : ℝ)|^4155 ≤ (8206307389581/25000000000000 : ℝ)^3131
        have hw : |(1079887227/2500000000 : ℝ)|=(1079887227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(734465099/2000000000 : ℝ)|^4155 ≤ (26463926422637/100000000000000 : ℝ)^3131
        have hw : |(734465099/2000000000 : ℝ)|=(734465099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080390251/10000000000 : ℝ)|^4155 ≤ (5088855500697/12500000000000 : ℝ)^3131
        have hw : |(5080390251/10000000000 : ℝ)|=(5080390251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-210706209/1000000000 : ℝ)*x 0 + (15646249/31250000 : ℝ)*x 1 + (5698238941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210706209/1000000000 : ℝ)^4155 ≤ (12661484044157/100000000000000 : ℝ)^3131 := by
    have hnat : (210706209 : ℕ)^4155*100000000000000^3131 ≤ 12661484044157^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210706209 1000000000 12661484044157 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15646249/31250000 : ℝ)^4155 ≤ (4991266725089/12500000000000 : ℝ)^3131 := by
    have hnat : (15646249 : ℕ)^4155*12500000000000^3131 ≤ 4991266725089^3131*31250000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15646249 31250000 4991266725089 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5698238941/10000000000 : ℝ)^4155 ≤ (47408382133887/100000000000000 : ℝ)^3131 := by
    have hnat : (5698238941 : ℕ)^4155*100000000000000^3131 ≤ 47408382133887^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5698238941 10000000000 47408382133887 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210706209/1000000000 : ℝ), (15646249/31250000 : ℝ), (5698238941/10000000000 : ℝ)] ![(12661484044157/100000000000000 : ℝ), (4991266725089/12500000000000 : ℝ), (47408382133887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210706209/1000000000 : ℝ)|^4155 ≤ (12661484044157/100000000000000 : ℝ)^3131
        have hw : |(-210706209/1000000000 : ℝ)|=(210706209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15646249/31250000 : ℝ)|^4155 ≤ (4991266725089/12500000000000 : ℝ)^3131
        have hw : |(15646249/31250000 : ℝ)|=(15646249/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5698238941/10000000000 : ℝ)|^4155 ≤ (47408382133887/100000000000000 : ℝ)^3131
        have hw : |(5698238941/10000000000 : ℝ)|=(5698238941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2619188169/5000000000 : ℝ)*x 0 + (-1789295199/10000000000 : ℝ)*x 1 + (712279841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619188169/5000000000 : ℝ)^4155 ≤ (5299921169267/12500000000000 : ℝ)^3131 := by
    have hnat : (2619188169 : ℕ)^4155*12500000000000^3131 ≤ 5299921169267^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619188169 5000000000 5299921169267 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1789295199/10000000000 : ℝ)^4155 ≤ (1019225085541/10000000000000 : ℝ)^3131 := by
    have hnat : (1789295199 : ℕ)^4155*10000000000000^3131 ≤ 1019225085541^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789295199 10000000000 1019225085541 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712279841/1250000000 : ℝ)^4155 ≤ (23704189891093/50000000000000 : ℝ)^3131 := by
    have hnat : (712279841 : ℕ)^4155*50000000000000^3131 ≤ 23704189891093^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712279841 1250000000 23704189891093 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619188169/5000000000 : ℝ), (-1789295199/10000000000 : ℝ), (712279841/1250000000 : ℝ)] ![(5299921169267/12500000000000 : ℝ), (1019225085541/10000000000000 : ℝ), (23704189891093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619188169/5000000000 : ℝ)|^4155 ≤ (5299921169267/12500000000000 : ℝ)^3131
        have hw : |(2619188169/5000000000 : ℝ)|=(2619188169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1789295199/10000000000 : ℝ)|^4155 ≤ (1019225085541/10000000000000 : ℝ)^3131
        have hw : |(-1789295199/10000000000 : ℝ)|=(1789295199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(712279841/1250000000 : ℝ)|^4155 ≤ (23704189891093/50000000000000 : ℝ)^3131
        have hw : |(712279841/1250000000 : ℝ)|=(712279841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523837637/1000000000 : ℝ)*x 0 + (2849119439/5000000000 : ℝ)*x 1 + (-1789294933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523837637/1000000000 : ℝ)^4155 ≤ (42399369697853/100000000000000 : ℝ)^3131 := by
    have hnat : (523837637 : ℕ)^4155*100000000000000^3131 ≤ 42399369697853^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523837637 1000000000 42399369697853 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2849119439/5000000000 : ℝ)^4155 ≤ (47408381438313/100000000000000 : ℝ)^3131 := by
    have hnat : (2849119439 : ℕ)^4155*100000000000000^3131 ≤ 47408381438313^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849119439 5000000000 47408381438313 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789294933/10000000000 : ℝ)^4155 ≤ (5096124422331/50000000000000 : ℝ)^3131 := by
    have hnat : (1789294933 : ℕ)^4155*50000000000000^3131 ≤ 5096124422331^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789294933 10000000000 5096124422331 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523837637/1000000000 : ℝ), (2849119439/5000000000 : ℝ), (-1789294933/10000000000 : ℝ)] ![(42399369697853/100000000000000 : ℝ), (47408381438313/100000000000000 : ℝ), (5096124422331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523837637/1000000000 : ℝ)|^4155 ≤ (42399369697853/100000000000000 : ℝ)^3131
        have hw : |(523837637/1000000000 : ℝ)|=(523837637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2849119439/5000000000 : ℝ)|^4155 ≤ (47408381438313/100000000000000 : ℝ)^3131
        have hw : |(2849119439/5000000000 : ℝ)|=(2849119439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789294933/10000000000 : ℝ)|^4155 ≤ (5096124422331/50000000000000 : ℝ)^3131
        have hw : |(-1789294933/10000000000 : ℝ)|=(1789294933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s1_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160606601/5000000000 : ℝ)*x 0 + (2530490403/5000000000 : ℝ)*x 1 + (3692122481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160606601/5000000000 : ℝ)^4155 ≤ (16421007151591/50000000000000 : ℝ)^3131 := by
    have hnat : (2160606601 : ℕ)^4155*50000000000000^3131 ≤ 16421007151591^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160606601 5000000000 16421007151591 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530490403/5000000000 : ℝ)^4155 ≤ (40504570965811/100000000000000 : ℝ)^3131 := by
    have hnat : (2530490403 : ℕ)^4155*100000000000000^3131 ≤ 40504570965811^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530490403 5000000000 40504570965811 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3692122481/10000000000 : ℝ)^4155 ≤ (6663353677371/25000000000000 : ℝ)^3131 := by
    have hnat : (3692122481 : ℕ)^4155*25000000000000^3131 ≤ 6663353677371^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3692122481 10000000000 6663353677371 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160606601/5000000000 : ℝ), (2530490403/5000000000 : ℝ), (3692122481/10000000000 : ℝ)] ![(16421007151591/50000000000000 : ℝ), (40504570965811/100000000000000 : ℝ), (6663353677371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160606601/5000000000 : ℝ)|^4155 ≤ (16421007151591/50000000000000 : ℝ)^3131
        have hw : |(2160606601/5000000000 : ℝ)|=(2160606601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530490403/5000000000 : ℝ)|^4155 ≤ (40504570965811/100000000000000 : ℝ)^3131
        have hw : |(2530490403/5000000000 : ℝ)|=(2530490403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3692122481/10000000000 : ℝ)|^4155 ≤ (6663353677371/25000000000000 : ℝ)^3131
        have hw : |(3692122481/10000000000 : ℝ)|=(3692122481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27911/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1377/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20551/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27911/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (31/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27911/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (31/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27911/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (31/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27911/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (31/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27911/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (31/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27911/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (31/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (31/10000 : ℝ) ^ (8309/2048 : ℝ) ≤ (6639433307/100000000000000000000 : ℝ) := by
    have hpowers : (31/10000 : ℝ)^8309 ≤ (6639433307/100000000000000000000 : ℝ)^2048 := by
      have hnat : (31 : ℕ)^8309*100000000000000000000^2048 ≤ 6639433307^2048*10000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 10000 6639433307 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/10000 : ℝ)) (X := (6639433307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27911/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (141052033054601897/25000000000000000000 : ℝ) := by
    have hpowers : (27911/100000 : ℝ)^8309 ≤ (141052033054601897/25000000000000000000 : ℝ)^2048 := by
      have hnat : (27911 : ℕ)^8309*25000000000000000000^2048 ≤ 141052033054601897^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27911 100000 141052033054601897 25000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27911/100000 : ℝ)) (X := (141052033054601897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000006639433307/50000000000000000000 : ℝ) ≤ (5000000000163649/5000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50000000006639433307/50000000000000000000 : ℝ)^2048 ≤ (5000000000163649/5000000000000000 : ℝ)^8309 := by
      have hnat : (50000000006639433307 : ℕ)^2048*5000000000000000^8309 ≤ 5000000000163649^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000006639433307 50000000000000000000 5000000000163649 5000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000163649/5000000000000000 : ℝ)) (X := (50000000006639433307/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20112841627771568179/20000000000000000000 : ℝ) ≤ (2002775424435117/2000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (20112841627771568179/20000000000000000000 : ℝ)^2048 ≤ (2002775424435117/2000000000000000 : ℝ)^8309 := by
      have hnat : (20112841627771568179 : ℕ)^2048*2000000000000000^8309 ≤ 2002775424435117^8309*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20112841627771568179 20000000000000000000 2002775424435117 2000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002775424435117/2000000000000000 : ℝ)) (X := (20112841627771568179/20000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12641052033054601897/12500000000000000000 : ℝ) ≤ (156683660062873/156250000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (12641052033054601897/12500000000000000000 : ℝ)^2048 ≤ (156683660062873/156250000000000 : ℝ)^8309 := by
      have hnat : (12641052033054601897 : ℕ)^2048*156250000000000^8309 ≤ 156683660062873^8309*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12641052033054601897 12500000000000000000 156683660062873 156250000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156683660062873/156250000000000 : ℝ)) (X := (12641052033054601897/12500000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6639433307/100000000000000000000 : ℝ) ≤ ((138000698096743907079/138005000000000000000 : ℝ)+2*(13877121848287/2760100000000000 : ℝ)*(31/10000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (138000698096743907079/138005000000000000000 : ℝ)+2*(13877121848287/2760100000000000 : ℝ)*(31/10000 : ℝ)=(5000000000163649/5000000000000000 : ℝ) by norm_num, show 1+2*(6639433307/100000000000000000000 : ℝ)=(50000000006639433307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(141052033054601897/25000000000000000000 : ℝ)+(6639433307/100000000000000000000 : ℝ) ≤ ((138000698096743907079/138005000000000000000 : ℝ)+(13877121848287/2760100000000000 : ℝ)*((27911/100000 : ℝ)+(31/10000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (138000698096743907079/138005000000000000000 : ℝ)+(13877121848287/2760100000000000 : ℝ)*((27911/100000 : ℝ)+(31/10000 : ℝ))=(2002775424435117/2000000000000000 : ℝ) by norm_num, show 1+(141052033054601897/25000000000000000000 : ℝ)+(6639433307/100000000000000000000 : ℝ)=(20112841627771568179/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(141052033054601897/25000000000000000000 : ℝ) ≤ ((138000698096743907079/138005000000000000000 : ℝ)+2*(13877121848287/2760100000000000 : ℝ)*(27911/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (138000698096743907079/138005000000000000000 : ℝ)+2*(13877121848287/2760100000000000 : ℝ)*(27911/100000 : ℝ)=(156683660062873/156250000000000 : ℝ) by norm_num, show 1+2*(141052033054601897/25000000000000000000 : ℝ)=(12641052033054601897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138000698096743907079/138005000000000000000 : ℝ)*(X 1 0+X 2 0)+(13877121848287/2760100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (31/10000 : ℝ)) (hi := (27911/100000 : ℝ)) (c := (138000698096743907079/138005000000000000000 : ℝ)) (alpha := (13877121848287/2760100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138000698096743907079/138005000000000000000 : ℝ)*(X 0 1+X 2 1)+(13877121848287/2760100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (31/10000 : ℝ)) (hi := (27911/100000 : ℝ)) (c := (138000698096743907079/138005000000000000000 : ℝ)) (alpha := (13877121848287/2760100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138000698096743907079/138005000000000000000 : ℝ)*(X 0 2+X 1 2)+(13877121848287/2760100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (31/10000 : ℝ)) (hi := (27911/100000 : ℝ)) (c := (138000698096743907079/138005000000000000000 : ℝ)) (alpha := (13877121848287/2760100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421244081/2000000000 : ℝ)*X 0 0+(5708239283/10000000000 : ℝ)*X 0 1+(4996995181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420496261/10000000000 : ℝ)*X 1 0+(-498107897/2000000000 : ℝ)*X 1 1+(1249248757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((54204977/100000000 : ℝ)*X 2 0+(2498496847/5000000000 : ℝ)*X 2 1+(-498107861/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079887227/2500000000 : ℝ)*X 0 0+(734465099/2000000000 : ℝ)*X 0 1+(5080390251/10000000000 : ℝ)*X 0 2+(1079887227/2500000000 : ℝ)*X 1 0+(734465099/2000000000 : ℝ)*X 1 1+(5080390251/10000000000 : ℝ)*X 1 2+(1079887227/2500000000 : ℝ)*X 2 0+(734465099/2000000000 : ℝ)*X 2 1+(5080390251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-210706209/1000000000 : ℝ)*X 0 0+(15646249/31250000 : ℝ)*X 0 1+(5698238941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619188169/5000000000 : ℝ)*X 1 0+(-1789295199/10000000000 : ℝ)*X 1 1+(712279841/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((523837637/1000000000 : ℝ)*X 2 0+(2849119439/5000000000 : ℝ)*X 2 1+(-1789294933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160606601/5000000000 : ℝ)*X 0 0+(2530490403/5000000000 : ℝ)*X 0 1+(3692122481/10000000000 : ℝ)*X 0 2+(2160606601/5000000000 : ℝ)*X 1 0+(2530490403/5000000000 : ℝ)*X 1 1+(3692122481/10000000000 : ℝ)*X 1 2+(2160606601/5000000000 : ℝ)*X 2 0+(2530490403/5000000000 : ℝ)*X 2 1+(3692122481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15696112486003865210514566037/1725062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65670181/20000000000000 : ℝ)*(base1) + (17094083/1000000000000 : ℝ)*(base19) + (2082664211/100000000000000 : ℝ)*(base23) + (84688823/100000000000000 : ℝ)*(upper3) + (30951331/12500000000000 : ℝ)*(upper5) + (264525256654033/25000000000000 : ℝ)*(major0) + (264525256654033/25000000000000 : ℝ)*(major1) + (264525256654033/25000000000000 : ℝ)*(major2) + (28119857230129/2000000000000 : ℝ)*(sp0) + (1405999165217513/100000000000000 : ℝ)*(sp1) + (1405998791961603/100000000000000 : ℝ)*(sp2) + (177549424320519/25000000000000 : ℝ)*(sp3) + (8341470269/100000000000000 : ℝ)*(sp4) + (2849677929/100000000000000 : ℝ)*(sp7) + (710200875310911/100000000000000 : ℝ)*(f.failure) + (1406000874625813/100000000000000 : ℝ)*(f.sum) + (102273879475927/69002500000000000000000000000 : ℝ)*base65 + (32765691657818149607/3450125000000000000000000000000000 : ℝ)*base67 + (2330145412588149607/3450125000000000000000000000000000 : ℝ)*base69 + (9714154499706274607/3450125000000000000000000000000000 : ℝ)*base71 + (809467782695939/138005000000000000000000000000 : ℝ)*base73 + (37039911358990024607/3450125000000000000000000000000000 : ℝ)*base75 + (19783019286280399607/3450125000000000000000000000000000 : ℝ)*base77 + (4907511708641649607/3450125000000000000000000000000000 : ℝ)*base79 + (5375527199583/69002500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6693209/5000000000000000000000 : ℝ)*base90 + (6693209/5000000000000000000000 : ℝ)*base92 + (6693209/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578844220898020658398086783/246437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8269371/25000000000000 : ℝ)*(base1) + (273333767/50000000000000 : ℝ)*(base19) + (71727589/12500000000000 : ℝ)*(base23) + (45483521/100000000000000 : ℝ)*(upper3) + (2469023/5000000000000 : ℝ)*(upper5) + (272099328555929/25000000000000 : ℝ)*(major0) + (272099328555929/25000000000000 : ℝ)*(major1) + (272099328555929/25000000000000 : ℝ)*(major2) + (998412897/50000000000000 : ℝ)*(sp1) + (50474051/2000000000000 : ℝ)*(sp2) + (1446258740428869/100000000000000 : ℝ)*(sp4) + (723128081929029/50000000000000 : ℝ)*(sp5) + (361563902457031/25000000000000 : ℝ)*(sp6) + (730535809723619/100000000000000 : ℝ)*(sp7) + (365267921400551/50000000000000 : ℝ)*(f.failure) + (723129353675693/50000000000000 : ℝ)*(f.sum) + (1537336507167/2464375000000000000000000000 : ℝ)*base65 + (4259383948065345913/492875000000000000000000000000000 : ℝ)*base67 + (4385437895457595913/492875000000000000000000000000000 : ℝ)*base69 + (3458714897239595913/492875000000000000000000000000000 : ℝ)*base71 + (39458080490863/9857500000000000000000000000 : ℝ)*base73 + (3392671954387470913/492875000000000000000000000000000 : ℝ)*base75 + (3350786587663845913/492875000000000000000000000000000 : ℝ)*base77 + (4957116205960845913/492875000000000000000000000000000 : ℝ)*base79 + (56732093516001/19715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (20912369/2500000000000000000000 : ℝ)*base90 + (20912369/2500000000000000000000 : ℝ)*base92 + (20912369/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1117_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27911/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20551/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1117_s2_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080404449/5000000000 : ℝ)*x 0 + (55156279/100000000 : ℝ)*x 1 + (5154920187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080404449/5000000000 : ℝ)^4155 ≤ (81824109321/625000000000 : ℝ)^3131 := by
    have hnat : (1080404449 : ℕ)^4155*625000000000^3131 ≤ 81824109321^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080404449 5000000000 81824109321 625000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55156279/100000000 : ℝ)^4155 ≤ (45402844148161/100000000000000 : ℝ)^3131 := by
    have hnat : (55156279 : ℕ)^4155*100000000000000^3131 ≤ 45402844148161^3131*100000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55156279 100000000 45402844148161 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5154920187/10000000000 : ℝ)^4155 ≤ (8301059669561/20000000000000 : ℝ)^3131 := by
    have hnat : (5154920187 : ℕ)^4155*20000000000000^3131 ≤ 8301059669561^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154920187 10000000000 8301059669561 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080404449/5000000000 : ℝ), (55156279/100000000 : ℝ), (5154920187/10000000000 : ℝ)] ![(81824109321/625000000000 : ℝ), (45402844148161/100000000000000 : ℝ), (8301059669561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080404449/5000000000 : ℝ)|^4155 ≤ (81824109321/625000000000 : ℝ)^3131
        have hw : |(-1080404449/5000000000 : ℝ)|=(1080404449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55156279/100000000 : ℝ)|^4155 ≤ (45402844148161/100000000000000 : ℝ)^3131
        have hw : |(55156279/100000000 : ℝ)|=(55156279/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5154920187/10000000000 : ℝ)|^4155 ≤ (8301059669561/20000000000000 : ℝ)^3131
        have hw : |(5154920187/10000000000 : ℝ)|=(5154920187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53749441/100000000 : ℝ)*x 0 + (-1174263363/5000000000 : ℝ)*x 1 + (322182599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53749441/100000000 : ℝ)^4155 ≤ (21936240644763/50000000000000 : ℝ)^3131 := by
    have hnat : (53749441 : ℕ)^4155*50000000000000^3131 ≤ 21936240644763^3131*100000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53749441 100000000 21936240644763 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1174263363/5000000000 : ℝ)^4155 ≤ (1827775678683/12500000000000 : ℝ)^3131 := by
    have hnat : (1174263363 : ℕ)^4155*12500000000000^3131 ≤ 1827775678683^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174263363 5000000000 1827775678683 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322182599/625000000 : ℝ)^4155 ≤ (41505313274579/100000000000000 : ℝ)^3131 := by
    have hnat : (322182599 : ℕ)^4155*100000000000000^3131 ≤ 41505313274579^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322182599 625000000 41505313274579 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53749441/100000000 : ℝ), (-1174263363/5000000000 : ℝ), (322182599/625000000 : ℝ)] ![(21936240644763/50000000000000 : ℝ), (1827775678683/12500000000000 : ℝ), (41505313274579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53749441/100000000 : ℝ)|^4155 ≤ (21936240644763/50000000000000 : ℝ)^3131
        have hw : |(53749441/100000000 : ℝ)|=(53749441/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1174263363/5000000000 : ℝ)|^4155 ≤ (1827775678683/12500000000000 : ℝ)^3131
        have hw : |(-1174263363/5000000000 : ℝ)|=(1174263363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322182599/625000000 : ℝ)|^4155 ≤ (41505313274579/100000000000000 : ℝ)^3131
        have hw : |(322182599/625000000 : ℝ)|=(322182599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374944029/10000000000 : ℝ)*x 0 + (5154921643/10000000000 : ℝ)*x 1 + (-2348526741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374944029/10000000000 : ℝ)^4155 ≤ (43872480520459/100000000000000 : ℝ)^3131 := by
    have hnat : (5374944029 : ℕ)^4155*100000000000000^3131 ≤ 43872480520459^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374944029 10000000000 43872480520459 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154921643/10000000000 : ℝ)^4155 ≤ (41505313904987/100000000000000 : ℝ)^3131 := by
    have hnat : (5154921643 : ℕ)^4155*100000000000000^3131 ≤ 41505313904987^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154921643 10000000000 41505313904987 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2348526741/10000000000 : ℝ)^4155 ≤ (73111027767/500000000000 : ℝ)^3131 := by
    have hnat : (2348526741 : ℕ)^4155*500000000000^3131 ≤ 73111027767^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348526741 10000000000 73111027767 500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374944029/10000000000 : ℝ), (5154921643/10000000000 : ℝ), (-2348526741/10000000000 : ℝ)] ![(43872480520459/100000000000000 : ℝ), (41505313904987/100000000000000 : ℝ), (73111027767/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374944029/10000000000 : ℝ)|^4155 ≤ (43872480520459/100000000000000 : ℝ)^3131
        have hw : |(5374944029/10000000000 : ℝ)|=(5374944029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154921643/10000000000 : ℝ)|^4155 ≤ (41505313904987/100000000000000 : ℝ)^3131
        have hw : |(5154921643/10000000000 : ℝ)|=(5154921643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2348526741/10000000000 : ℝ)|^4155 ≤ (73111027767/500000000000 : ℝ)^3131
        have hw : |(-2348526741/10000000000 : ℝ)|=(2348526741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4356932603/10000000000 : ℝ)*x 0 + (4014465559/10000000000 : ℝ)*x 1 + (1182140919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356932603/10000000000 : ℝ)^4155 ≤ (33202760517647/100000000000000 : ℝ)^3131 := by
    have hnat : (4356932603 : ℕ)^4155*100000000000000^3131 ≤ 33202760517647^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356932603 10000000000 33202760517647 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014465559/10000000000 : ℝ)^4155 ≤ (2978470966113/10000000000000 : ℝ)^3131 := by
    have hnat : (4014465559 : ℕ)^4155*10000000000000^3131 ≤ 2978470966113^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014465559 10000000000 2978470966113 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182140919/2500000000 : ℝ)^4155 ≤ (37012529808561/100000000000000 : ℝ)^3131 := by
    have hnat : (1182140919 : ℕ)^4155*100000000000000^3131 ≤ 37012529808561^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182140919 2500000000 37012529808561 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356932603/10000000000 : ℝ), (4014465559/10000000000 : ℝ), (1182140919/2500000000 : ℝ)] ![(33202760517647/100000000000000 : ℝ), (2978470966113/10000000000000 : ℝ), (37012529808561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356932603/10000000000 : ℝ)|^4155 ≤ (33202760517647/100000000000000 : ℝ)^3131
        have hw : |(4356932603/10000000000 : ℝ)|=(4356932603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014465559/10000000000 : ℝ)|^4155 ≤ (2978470966113/10000000000000 : ℝ)^3131
        have hw : |(4014465559/10000000000 : ℝ)|=(4014465559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1182140919/2500000000 : ℝ)|^4155 ≤ (37012529808561/100000000000000 : ℝ)^3131
        have hw : |(1182140919/2500000000 : ℝ)|=(1182140919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080459163/5000000000 : ℝ)*x 0 + (5157451787/10000000000 : ℝ)*x 1 + (5513070747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080459163/5000000000 : ℝ)^4155 ≤ (13092737333843/100000000000000 : ℝ)^3131 := by
    have hnat : (1080459163 : ℕ)^4155*100000000000000^3131 ≤ 13092737333843^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080459163 5000000000 13092737333843 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157451787/10000000000 : ℝ)^4155 ≤ (20766175178119/50000000000000 : ℝ)^3131 := by
    have hnat : (5157451787 : ℕ)^4155*50000000000000^3131 ≤ 20766175178119^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157451787 10000000000 20766175178119 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513070747/10000000000 : ℝ)^4155 ≤ (45374912289027/100000000000000 : ℝ)^3131 := by
    have hnat : (5513070747 : ℕ)^4155*100000000000000^3131 ≤ 45374912289027^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513070747 10000000000 45374912289027 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080459163/5000000000 : ℝ), (5157451787/10000000000 : ℝ), (5513070747/10000000000 : ℝ)] ![(13092737333843/100000000000000 : ℝ), (20766175178119/50000000000000 : ℝ), (45374912289027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080459163/5000000000 : ℝ)|^4155 ≤ (13092737333843/100000000000000 : ℝ)^3131
        have hw : |(-1080459163/5000000000 : ℝ)|=(1080459163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157451787/10000000000 : ℝ)|^4155 ≤ (20766175178119/50000000000000 : ℝ)^3131
        have hw : |(5157451787/10000000000 : ℝ)|=(5157451787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513070747/10000000000 : ℝ)|^4155 ≤ (45374912289027/100000000000000 : ℝ)^3131
        have hw : |(5513070747/10000000000 : ℝ)|=(5513070747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5283576793/10000000000 : ℝ)*x 0 + (-1990376889/10000000000 : ℝ)*x 1 + (1378267707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283576793/10000000000 : ℝ)^4155 ≤ (42885557822547/100000000000000 : ℝ)^3131 := by
    have hnat : (5283576793 : ℕ)^4155*100000000000000^3131 ≤ 42885557822547^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283576793 10000000000 42885557822547 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1990376889/10000000000 : ℝ)^4155 ≤ (1467441123543/12500000000000 : ℝ)^3131 := by
    have hnat : (1990376889 : ℕ)^4155*12500000000000^3131 ≤ 1467441123543^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990376889 10000000000 1467441123543 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378267707/2500000000 : ℝ)^4155 ≤ (22687456586863/50000000000000 : ℝ)^3131 := by
    have hnat : (1378267707 : ℕ)^4155*50000000000000^3131 ≤ 22687456586863^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378267707 2500000000 22687456586863 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283576793/10000000000 : ℝ), (-1990376889/10000000000 : ℝ), (1378267707/2500000000 : ℝ)] ![(42885557822547/100000000000000 : ℝ), (1467441123543/12500000000000 : ℝ), (22687456586863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283576793/10000000000 : ℝ)|^4155 ≤ (42885557822547/100000000000000 : ℝ)^3131
        have hw : |(5283576793/10000000000 : ℝ)|=(5283576793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1990376889/10000000000 : ℝ)|^4155 ≤ (1467441123543/12500000000000 : ℝ)^3131
        have hw : |(-1990376889/10000000000 : ℝ)|=(1990376889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378267707/2500000000 : ℝ)|^4155 ≤ (22687456586863/50000000000000 : ℝ)^3131
        have hw : |(1378267707/2500000000 : ℝ)|=(1378267707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5283576913/10000000000 : ℝ)*x 0 + (5513070783/10000000000 : ℝ)*x 1 + (-1990376787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283576913/10000000000 : ℝ)^4155 ≤ (42885559115111/100000000000000 : ℝ)^3131 := by
    have hnat : (5283576913 : ℕ)^4155*100000000000000^3131 ≤ 42885559115111^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283576913 10000000000 42885559115111 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513070783/10000000000 : ℝ)^4155 ≤ (45374912682227/100000000000000 : ℝ)^3131 := by
    have hnat : (5513070783 : ℕ)^4155*100000000000000^3131 ≤ 45374912682227^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513070783 10000000000 45374912682227 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990376787/10000000000 : ℝ)^4155 ≤ (1467441023747/12500000000000 : ℝ)^3131 := by
    have hnat : (1990376787 : ℕ)^4155*12500000000000^3131 ≤ 1467441023747^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990376787 10000000000 1467441023747 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283576913/10000000000 : ℝ), (5513070783/10000000000 : ℝ), (-1990376787/10000000000 : ℝ)] ![(42885559115111/100000000000000 : ℝ), (45374912682227/100000000000000 : ℝ), (1467441023747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283576913/10000000000 : ℝ)|^4155 ≤ (42885559115111/100000000000000 : ℝ)^3131
        have hw : |(5283576913/10000000000 : ℝ)|=(5283576913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513070783/10000000000 : ℝ)|^4155 ≤ (45374912682227/100000000000000 : ℝ)^3131
        have hw : |(5513070783/10000000000 : ℝ)|=(5513070783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990376787/10000000000 : ℝ)|^4155 ≤ (1467441023747/12500000000000 : ℝ)^3131
        have hw : |(-1990376787/10000000000 : ℝ)|=(1990376787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_s2_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4357150667/10000000000 : ℝ)*x 0 + (188942129/400000000 : ℝ)*x 1 + (200976283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357150667/10000000000 : ℝ)^4155 ≤ (33204965823551/100000000000000 : ℝ)^3131 := by
    have hnat : (4357150667 : ℕ)^4155*100000000000000^3131 ≤ 33204965823551^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357150667 10000000000 33204965823551 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188942129/400000000 : ℝ)^4155 ≤ (7392098638859/20000000000000 : ℝ)^3131 := by
    have hnat : (188942129 : ℕ)^4155*20000000000000^3131 ≤ 7392098638859^3131*400000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188942129 400000000 7392098638859 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200976283/500000000 : ℝ)^4155 ≤ (3729317620791/12500000000000 : ℝ)^3131 := by
    have hnat : (200976283 : ℕ)^4155*12500000000000^3131 ≤ 3729317620791^3131*500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200976283 500000000 3729317620791 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357150667/10000000000 : ℝ), (188942129/400000000 : ℝ), (200976283/500000000 : ℝ)] ![(33204965823551/100000000000000 : ℝ), (7392098638859/20000000000000 : ℝ), (3729317620791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357150667/10000000000 : ℝ)|^4155 ≤ (33204965823551/100000000000000 : ℝ)^3131
        have hw : |(4357150667/10000000000 : ℝ)|=(4357150667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188942129/400000000 : ℝ)|^4155 ≤ (7392098638859/20000000000000 : ℝ)^3131
        have hw : |(188942129/400000000 : ℝ)|=(188942129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200976283/500000000 : ℝ)|^4155 ≤ (3729317620791/12500000000000 : ℝ)^3131
        have hw : |(200976283/500000000 : ℝ)|=(200976283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2239/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8289/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1377/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1377/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1377/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1377/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1377/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1377/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1377/25000 : ℝ) ^ (8309/2048 : ℝ) ≤ (779920052629727/100000000000000000000 : ℝ) := by
    have hpowers : (1377/25000 : ℝ)^8309 ≤ (779920052629727/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1377 : ℕ)^8309*100000000000000000000^2048 ≤ 779920052629727^2048*25000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1377 25000 779920052629727 100000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1377/25000 : ℝ)) (X := (779920052629727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20551/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (81478821705341297/50000000000000000000 : ℝ) := by
    have hpowers : (20551/100000 : ℝ)^8309 ≤ (81478821705341297/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20551 : ℕ)^8309*50000000000000000000^2048 ≤ 81478821705341297^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20551 100000 81478821705341297 50000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20551/100000 : ℝ)) (X := (81478821705341297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000779920052629727/50000000000000000000 : ℝ) ≤ (10000038446669417/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (50000779920052629727/50000000000000000000 : ℝ)^2048 ≤ (10000038446669417/10000000000000000 : ℝ)^8309 := by
      have hnat : (50000779920052629727 : ℕ)^2048*10000000000000000^8309 ≤ 10000038446669417^8309*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000779920052629727 50000000000000000000 10000038446669417 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000038446669417/10000000000000000 : ℝ)) (X := (50000779920052629727/50000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100163737563463312321/100000000000000000000 : ℝ) ≤ (10004033311596769/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (100163737563463312321/100000000000000000000 : ℝ)^2048 ≤ (10004033311596769/10000000000000000 : ℝ)^8309 := by
      have hnat : (100163737563463312321 : ℕ)^2048*10000000000000000^8309 ≤ 10004033311596769^8309*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100163737563463312321 100000000000000000000 10004033311596769 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004033311596769/10000000000000000 : ℝ)) (X := (100163737563463312321/100000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25081478821705341297/25000000000000000000 : ℝ) ≤ (10008028176524121/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (25081478821705341297/25000000000000000000 : ℝ)^2048 ≤ (10008028176524121/10000000000000000 : ℝ)^8309 := by
      have hnat : (25081478821705341297 : ℕ)^2048*10000000000000000^8309 ≤ 10008028176524121^8309*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25081478821705341297 25000000000000000000 10008028176524121 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008028176524121/10000000000000000 : ℝ)) (X := (25081478821705341297/25000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(779920052629727/100000000000000000000 : ℝ) ≤ ((150386570921208330299/150430000000000000000 : ℝ)+2*(499358115919/188037500000000 : ℝ)*(1377/25000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (150386570921208330299/150430000000000000000 : ℝ)+2*(499358115919/188037500000000 : ℝ)*(1377/25000 : ℝ)=(10000038446669417/10000000000000000 : ℝ) by norm_num, show 1+2*(779920052629727/100000000000000000000 : ℝ)=(50000779920052629727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81478821705341297/50000000000000000000 : ℝ)+(779920052629727/100000000000000000000 : ℝ) ≤ ((150386570921208330299/150430000000000000000 : ℝ)+(499358115919/188037500000000 : ℝ)*((20551/100000 : ℝ)+(1377/25000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (150386570921208330299/150430000000000000000 : ℝ)+(499358115919/188037500000000 : ℝ)*((20551/100000 : ℝ)+(1377/25000 : ℝ))=(10004033311596769/10000000000000000 : ℝ) by norm_num, show 1+(81478821705341297/50000000000000000000 : ℝ)+(779920052629727/100000000000000000000 : ℝ)=(100163737563463312321/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81478821705341297/50000000000000000000 : ℝ) ≤ ((150386570921208330299/150430000000000000000 : ℝ)+2*(499358115919/188037500000000 : ℝ)*(20551/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (150386570921208330299/150430000000000000000 : ℝ)+2*(499358115919/188037500000000 : ℝ)*(20551/100000 : ℝ)=(10008028176524121/10000000000000000 : ℝ) by norm_num, show 1+2*(81478821705341297/50000000000000000000 : ℝ)=(25081478821705341297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (150386570921208330299/150430000000000000000 : ℝ)*(X 1 0+X 2 0)+(499358115919/188037500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (1377/25000 : ℝ)) (hi := (20551/100000 : ℝ)) (c := (150386570921208330299/150430000000000000000 : ℝ)) (alpha := (499358115919/188037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (150386570921208330299/150430000000000000000 : ℝ)*(X 0 1+X 2 1)+(499358115919/188037500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (1377/25000 : ℝ)) (hi := (20551/100000 : ℝ)) (c := (150386570921208330299/150430000000000000000 : ℝ)) (alpha := (499358115919/188037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (150386570921208330299/150430000000000000000 : ℝ)*(X 0 2+X 1 2)+(499358115919/188037500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (1377/25000 : ℝ)) (hi := (20551/100000 : ℝ)) (c := (150386570921208330299/150430000000000000000 : ℝ)) (alpha := (499358115919/188037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080404449/5000000000 : ℝ)*X 0 0+(55156279/100000000 : ℝ)*X 0 1+(5154920187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53749441/100000000 : ℝ)*X 1 0+(-1174263363/5000000000 : ℝ)*X 1 1+(322182599/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374944029/10000000000 : ℝ)*X 2 0+(5154921643/10000000000 : ℝ)*X 2 1+(-2348526741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356932603/10000000000 : ℝ)*X 0 0+(4014465559/10000000000 : ℝ)*X 0 1+(1182140919/2500000000 : ℝ)*X 0 2+(4356932603/10000000000 : ℝ)*X 1 0+(4014465559/10000000000 : ℝ)*X 1 1+(1182140919/2500000000 : ℝ)*X 1 2+(4356932603/10000000000 : ℝ)*X 2 0+(4014465559/10000000000 : ℝ)*X 2 1+(1182140919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080459163/5000000000 : ℝ)*X 0 0+(5157451787/10000000000 : ℝ)*X 0 1+(5513070747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283576793/10000000000 : ℝ)*X 1 0+(-1990376889/10000000000 : ℝ)*X 1 1+(1378267707/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283576913/10000000000 : ℝ)*X 2 0+(5513070783/10000000000 : ℝ)*X 2 1+(-1990376787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357150667/10000000000 : ℝ)*X 0 0+(188942129/400000000 : ℝ)*X 0 1+(200976283/500000000 : ℝ)*X 0 2+(4357150667/10000000000 : ℝ)*X 1 0+(188942129/400000000 : ℝ)*X 1 1+(200976283/500000000 : ℝ)*X 1 2+(4357150667/10000000000 : ℝ)*X 2 0+(188942129/400000000 : ℝ)*X 2 1+(200976283/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373985547416024078104669581/107450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6823731/10000000000000 : ℝ)*(base29) + (48667393/50000000000000 : ℝ)*(upper2) + (18172491/100000000000000 : ℝ)*(upper3) + (38825563/50000000000000 : ℝ)*(upper4) + (2843459/10000000000000 : ℝ)*(upper5) + (208635859378309/10000000000000 : ℝ)*(major0) + (5215896655051/250000000000 : ℝ)*(major1) + (5215896655051/250000000000 : ℝ)*(major2) + (1386168555018649/50000000000000 : ℝ)*(sp0) + (1386173185554457/50000000000000 : ℝ)*(sp1) + (1386173185554457/50000000000000 : ℝ)*(sp2) + (700184684538557/50000000000000 : ℝ)*(sp3) + (4664654463/50000000000000 : ℝ)*(sp4) + (349899743/25000000000000 : ℝ)*(sp7) + (700185384338043/50000000000000 : ℝ)*(f.failure) + (110893857573849/4000000000000 : ℝ)*(f.sum) + (33658791838519/7521500000000000000000000000 : ℝ)*base66 + (6228285432309801/767500000000000000000000000000 : ℝ)*base67 + (3473583148039801/767500000000000000000000000000 : ℝ)*base69 + (27469887606172284391/1504300000000000000000000000000000 : ℝ)*base71 + (11319692728109/7521500000000000000000000000 : ℝ)*base74 + (239588192665410249/37607500000000000000000000000000 : ℝ)*base75 + (15960086498616484391/1504300000000000000000000000000000 : ℝ)*base77 + (353057738427850249/37607500000000000000000000000000 : ℝ)*base79 + (36403123883241/7521500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31419517/2500000000000000000000 : ℝ)*base90 + (31419517/2500000000000000000000 : ℝ)*base92 + (31419517/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1805388069472153470010426221/376075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195091001/20000000000000 : ℝ)*(base19) + (1145032483/100000000000000 : ℝ)*(base23) + (139557161/100000000000000 : ℝ)*(upper3) + (17202059/50000000000000 : ℝ)*(lower4) + (20985111/25000000000000 : ℝ)*(upper5) + (105809928487493/5000000000000 : ℝ)*(major0) + (105809928487493/5000000000000 : ℝ)*(major1) + (105809928487493/5000000000000 : ℝ)*(major2) + (111999319/1250000000000 : ℝ)*(sp1) + (11307579887/100000000000000 : ℝ)*(sp2) + (35149969587281/1250000000000 : ℝ)*(sp4) + (1405993815790977/50000000000000 : ℝ)*(sp5) + (281198511437011/10000000000000 : ℝ)*(sp6) + (1420399412497021/100000000000000 : ℝ)*(sp7) + (1420399412497021/100000000000000 : ℝ)*(f.failure) + (35149969587281/1250000000000 : ℝ)*(f.sum) + (79430483055517/15043000000000000000000000000 : ℝ)*base66 + (26812860081536743/15350000000000000000000000000000 : ℝ)*base67 + (48594581870713257/15350000000000000000000000000000 : ℝ)*base70 + (85442519493863257/15350000000000000000000000000000 : ℝ)*base72 + (7222017142887/15043000000000000000000000000 : ℝ)*base73 + (88769052488086743/15350000000000000000000000000000 : ℝ)*base75 + (65901810329713257/15350000000000000000000000000000 : ℝ)*base78 + (14073380132313257/15350000000000000000000000000000 : ℝ)*base80 + (4372523607231/3008600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2388299/5000000000000000000000 : ℝ)*base90 + (2388299/5000000000000000000000 : ℝ)*base92 + (2388299/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1117_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1117_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1117_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1117_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1117_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2239/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8289/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
