-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:43.559237+00:00
-- url     : https://prove2.me/submissions/d75593ac-4332-44a1-b469-403e4f705d05

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
theorem support_rectangle_w1095_s3_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185209793/10000000000 : ℝ)*x 0 + (5434221881/10000000000 : ℝ)*x 1 + (1045490039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185209793/10000000000 : ℝ)^259 ≤ (3316281647617/25000000000000 : ℝ)^195 := by
    have hnat : (2185209793 : ℕ)^259*25000000000000^195 ≤ 3316281647617^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185209793 10000000000 3316281647617 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434221881/10000000000 : ℝ)^259 ≤ (44484436373907/100000000000000 : ℝ)^195 := by
    have hnat : (5434221881 : ℕ)^259*100000000000000^195 ≤ 44484436373907^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434221881 10000000000 44484436373907 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045490039/2000000000 : ℝ)^259 ≤ (10562609255149/25000000000000 : ℝ)^195 := by
    have hnat : (1045490039 : ℕ)^259*25000000000000^195 ≤ 10562609255149^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045490039 2000000000 10562609255149 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185209793/10000000000 : ℝ), (5434221881/10000000000 : ℝ), (1045490039/2000000000 : ℝ)] ![(3316281647617/25000000000000 : ℝ), (44484436373907/100000000000000 : ℝ), (10562609255149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185209793/10000000000 : ℝ)|^259 ≤ (3316281647617/25000000000000 : ℝ)^195
        have hw : |(-2185209793/10000000000 : ℝ)|=(2185209793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434221881/10000000000 : ℝ)|^259 ≤ (44484436373907/100000000000000 : ℝ)^195
        have hw : |(5434221881/10000000000 : ℝ)|=(5434221881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045490039/2000000000 : ℝ)|^259 ≤ (10562609255149/25000000000000 : ℝ)^195
        have hw : |(1045490039/2000000000 : ℝ)|=(1045490039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2677475597/5000000000 : ℝ)*x 0 + (-2291018331/10000000000 : ℝ)*x 1 + (5227450057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677475597/5000000000 : ℝ)^259 ≤ (43624622976023/100000000000000 : ℝ)^195 := by
    have hnat : (2677475597 : ℕ)^259*100000000000000^195 ≤ 43624622976023^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677475597 5000000000 43624622976023 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291018331/10000000000 : ℝ)^259 ≤ (3531235367813/25000000000000 : ℝ)^195 := by
    have hnat : (2291018331 : ℕ)^259*25000000000000^195 ≤ 3531235367813^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291018331 10000000000 3531235367813 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227450057/10000000000 : ℝ)^259 ≤ (42250435539151/100000000000000 : ℝ)^195 := by
    have hnat : (5227450057 : ℕ)^259*100000000000000^195 ≤ 42250435539151^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227450057 10000000000 42250435539151 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677475597/5000000000 : ℝ), (-2291018331/10000000000 : ℝ), (5227450057/10000000000 : ℝ)] ![(43624622976023/100000000000000 : ℝ), (3531235367813/25000000000000 : ℝ), (42250435539151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677475597/5000000000 : ℝ)|^259 ≤ (43624622976023/100000000000000 : ℝ)^195
        have hw : |(2677475597/5000000000 : ℝ)|=(2677475597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2291018331/10000000000 : ℝ)|^259 ≤ (3531235367813/25000000000000 : ℝ)^195
        have hw : |(-2291018331/10000000000 : ℝ)|=(2291018331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227450057/10000000000 : ℝ)|^259 ≤ (42250435539151/100000000000000 : ℝ)^195
        have hw : |(5227450057/10000000000 : ℝ)|=(5227450057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5354951063/10000000000 : ℝ)*x 0 + (5227450507/10000000000 : ℝ)*x 1 + (-458203583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354951063/10000000000 : ℝ)^259 ≤ (21812310779279/50000000000000 : ℝ)^195 := by
    have hnat : (5354951063 : ℕ)^259*50000000000000^195 ≤ 21812310779279^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354951063 10000000000 21812310779279 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227450507/10000000000 : ℝ)^259 ≤ (845008807399/2000000000000 : ℝ)^195 := by
    have hnat : (5227450507 : ℕ)^259*2000000000000^195 ≤ 845008807399^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227450507 10000000000 845008807399 2000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458203583/2000000000 : ℝ)^259 ≤ (882808629043/6250000000000 : ℝ)^195 := by
    have hnat : (458203583 : ℕ)^259*6250000000000^195 ≤ 882808629043^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458203583 2000000000 882808629043 6250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354951063/10000000000 : ℝ), (5227450507/10000000000 : ℝ), (-458203583/2000000000 : ℝ)] ![(21812310779279/50000000000000 : ℝ), (845008807399/2000000000000 : ℝ), (882808629043/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354951063/10000000000 : ℝ)|^259 ≤ (21812310779279/50000000000000 : ℝ)^195
        have hw : |(5354951063/10000000000 : ℝ)|=(5354951063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227450507/10000000000 : ℝ)|^259 ≤ (845008807399/2000000000000 : ℝ)^195
        have hw : |(5227450507/10000000000 : ℝ)|=(5227450507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458203583/2000000000 : ℝ)|^259 ≤ (882808629043/6250000000000 : ℝ)^195
        have hw : |(-458203583/2000000000 : ℝ)|=(458203583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2184378421/5000000000 : ℝ)*x 0 + (2084871537/5000000000 : ℝ)*x 1 + (143041261/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184378421/5000000000 : ℝ)^259 ≤ (8322647324121/25000000000000 : ℝ)^195 := by
    have hnat : (2184378421 : ℕ)^259*25000000000000^195 ≤ 8322647324121^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184378421 5000000000 8322647324121 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084871537/5000000000 : ℝ)^259 ≤ (31291560280871/100000000000000 : ℝ)^195 := by
    have hnat : (2084871537 : ℕ)^259*100000000000000^195 ≤ 31291560280871^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084871537 5000000000 31291560280871 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143041261/312500000 : ℝ)^259 ≤ (35417850409317/100000000000000 : ℝ)^195 := by
    have hnat : (143041261 : ℕ)^259*100000000000000^195 ≤ 35417850409317^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143041261 312500000 35417850409317 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184378421/5000000000 : ℝ), (2084871537/5000000000 : ℝ), (143041261/312500000 : ℝ)] ![(8322647324121/25000000000000 : ℝ), (31291560280871/100000000000000 : ℝ), (35417850409317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184378421/5000000000 : ℝ)|^259 ≤ (8322647324121/25000000000000 : ℝ)^195
        have hw : |(2184378421/5000000000 : ℝ)|=(2184378421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084871537/5000000000 : ℝ)|^259 ≤ (31291560280871/100000000000000 : ℝ)^195
        have hw : |(2084871537/5000000000 : ℝ)|=(2084871537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143041261/312500000 : ℝ)|^259 ≤ (35417850409317/100000000000000 : ℝ)^195
        have hw : |(143041261/312500000 : ℝ)|=(143041261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-546307619/2500000000 : ℝ)*x 0 + (5228279977/10000000000 : ℝ)*x 1 + (5433387217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546307619/2500000000 : ℝ)^259 ≤ (1326529335267/10000000000000 : ℝ)^195 := by
    have hnat : (546307619 : ℕ)^259*10000000000000^195 ≤ 1326529335267^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546307619 2500000000 1326529335267 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228279977/10000000000 : ℝ)^259 ≤ (42259345052761/100000000000000 : ℝ)^195 := by
    have hnat : (5228279977 : ℕ)^259*100000000000000^195 ≤ 42259345052761^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228279977 10000000000 42259345052761 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433387217/10000000000 : ℝ)^259 ≤ (22237680791643/50000000000000 : ℝ)^195 := by
    have hnat : (5433387217 : ℕ)^259*50000000000000^195 ≤ 22237680791643^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433387217 10000000000 22237680791643 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546307619/2500000000 : ℝ), (5228279977/10000000000 : ℝ), (5433387217/10000000000 : ℝ)] ![(1326529335267/10000000000000 : ℝ), (42259345052761/100000000000000 : ℝ), (22237680791643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546307619/2500000000 : ℝ)|^259 ≤ (1326529335267/10000000000000 : ℝ)^195
        have hw : |(-546307619/2500000000 : ℝ)|=(546307619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228279977/10000000000 : ℝ)|^259 ≤ (42259345052761/100000000000000 : ℝ)^195
        have hw : |(5228279977/10000000000 : ℝ)|=(5228279977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433387217/10000000000 : ℝ)|^259 ≤ (22237680791643/50000000000000 : ℝ)^195
        have hw : |(5433387217/10000000000 : ℝ)|=(5433387217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (265137477/500000000 : ℝ)*x 0 + (-1042540527/5000000000 : ℝ)*x 1 + (135834687/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265137477/500000000 : ℝ)^259 ≤ (10765172089651/25000000000000 : ℝ)^195 := by
    have hnat : (265137477 : ℕ)^259*25000000000000^195 ≤ 10765172089651^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265137477 500000000 10765172089651 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042540527/5000000000 : ℝ)^259 ≤ (6231973592191/50000000000000 : ℝ)^195 := by
    have hnat : (1042540527 : ℕ)^259*50000000000000^195 ≤ 6231973592191^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042540527 5000000000 6231973592191 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135834687/250000000 : ℝ)^259 ≤ (44475364442651/100000000000000 : ℝ)^195 := by
    have hnat : (135834687 : ℕ)^259*100000000000000^195 ≤ 44475364442651^195*250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135834687 250000000 44475364442651 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265137477/500000000 : ℝ), (-1042540527/5000000000 : ℝ), (135834687/250000000 : ℝ)] ![(10765172089651/25000000000000 : ℝ), (6231973592191/50000000000000 : ℝ), (44475364442651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265137477/500000000 : ℝ)|^259 ≤ (10765172089651/25000000000000 : ℝ)^195
        have hw : |(265137477/500000000 : ℝ)|=(265137477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042540527/5000000000 : ℝ)|^259 ≤ (6231973592191/50000000000000 : ℝ)^195
        have hw : |(-1042540527/5000000000 : ℝ)|=(1042540527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135834687/250000000 : ℝ)|^259 ≤ (44475364442651/100000000000000 : ℝ)^195
        have hw : |(135834687/250000000 : ℝ)|=(135834687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (165710927/312500000 : ℝ)*x 0 + (135834681/250000000 : ℝ)*x 1 + (-1042540607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165710927/312500000 : ℝ)^259 ≤ (43060689696021/100000000000000 : ℝ)^195 := by
    have hnat : (165710927 : ℕ)^259*100000000000000^195 ≤ 43060689696021^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165710927 312500000 43060689696021 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135834681/250000000 : ℝ)^259 ≤ (347463764323/781250000000 : ℝ)^195 := by
    have hnat : (135834681 : ℕ)^259*781250000000^195 ≤ 347463764323^195*250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135834681 250000000 347463764323 781250000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042540607/5000000000 : ℝ)^259 ≤ (3115987113679/25000000000000 : ℝ)^195 := by
    have hnat : (1042540607 : ℕ)^259*25000000000000^195 ≤ 3115987113679^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042540607 5000000000 3115987113679 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165710927/312500000 : ℝ), (135834681/250000000 : ℝ), (-1042540607/5000000000 : ℝ)] ![(43060689696021/100000000000000 : ℝ), (347463764323/781250000000 : ℝ), (3115987113679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165710927/312500000 : ℝ)|^259 ≤ (43060689696021/100000000000000 : ℝ)^195
        have hw : |(165710927/312500000 : ℝ)|=(165710927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135834681/250000000 : ℝ)|^259 ≤ (347463764323/781250000000 : ℝ)^195
        have hw : |(135834681/250000000 : ℝ)|=(135834681/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042540607/5000000000 : ℝ)|^259 ≤ (3115987113679/25000000000000 : ℝ)^195
        have hw : |(-1042540607/5000000000 : ℝ)|=(1042540607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s3_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4368797181/10000000000 : ℝ)*x 0 + (4575685491/10000000000 : ℝ)*x 1 + (2085693791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368797181/10000000000 : ℝ)^259 ≤ (1664549878657/5000000000000 : ℝ)^195 := by
    have hnat : (4368797181 : ℕ)^259*5000000000000^195 ≤ 1664549878657^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368797181 10000000000 1664549878657 5000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4575685491/10000000000 : ℝ)^259 ≤ (8850262388229/25000000000000 : ℝ)^195 := by
    have hnat : (4575685491 : ℕ)^259*25000000000000^195 ≤ 8850262388229^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575685491 10000000000 8850262388229 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085693791/5000000000 : ℝ)^259 ≤ (15653976427767/50000000000000 : ℝ)^195 := by
    have hnat : (2085693791 : ℕ)^259*50000000000000^195 ≤ 15653976427767^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085693791 5000000000 15653976427767 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368797181/10000000000 : ℝ), (4575685491/10000000000 : ℝ), (2085693791/5000000000 : ℝ)] ![(1664549878657/5000000000000 : ℝ), (8850262388229/25000000000000 : ℝ), (15653976427767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368797181/10000000000 : ℝ)|^259 ≤ (1664549878657/5000000000000 : ℝ)^195
        have hw : |(4368797181/10000000000 : ℝ)|=(4368797181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4575685491/10000000000 : ℝ)|^259 ≤ (8850262388229/25000000000000 : ℝ)^195
        have hw : |(4575685491/10000000000 : ℝ)|=(4575685491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085693791/5000000000 : ℝ)|^259 ≤ (15653976427767/50000000000000 : ℝ)^195
        have hw : |(2085693791/5000000000 : ℝ)|=(2085693791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1049/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2973/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16647/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2213/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16647/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2213/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16647/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2213/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16647/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2213/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16647/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2213/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16647/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2213/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2213/25000 : ℝ) ^ (8287/2048 : ℝ) ≤ (274342019439743/5000000000000000000 : ℝ) := by
    have hpowers : (2213/25000 : ℝ)^8287 ≤ (274342019439743/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2213 : ℕ)^8287*5000000000000000000^2048 ≤ 274342019439743^2048*25000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2213 25000 274342019439743 5000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2213/25000 : ℝ)) (X := (274342019439743/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16647/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (14133647151184541/20000000000000000000 : ℝ) := by
    have hpowers : (16647/100000 : ℝ)^8287 ≤ (14133647151184541/20000000000000000000 : ℝ)^2048 := by
      have hnat : (16647 : ℕ)^8287*20000000000000000000^2048 ≤ 14133647151184541^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16647 100000 14133647151184541 20000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16647/100000 : ℝ)) (X := (14133647151184541/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500274342019439743/2500000000000000000 : ℝ) ≤ (10000271185832263/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (2500274342019439743/2500000000000000000 : ℝ)^2048 ≤ (10000271185832263/10000000000000000 : ℝ)^8287 := by
      have hnat : (2500274342019439743 : ℕ)^2048*10000000000000000^8287 ≤ 10000271185832263^8287*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500274342019439743 2500000000000000000 10000271185832263 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000271185832263/10000000000000000 : ℝ)) (X := (2500274342019439743/2500000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20015231015228943513/20000000000000000000 : ℝ) ≤ (10001881512063869/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (20015231015228943513/20000000000000000000 : ℝ)^2048 ≤ (10001881512063869/10000000000000000 : ℝ)^8287 := by
      have hnat : (20015231015228943513 : ℕ)^2048*10000000000000000^8287 ≤ 10001881512063869^8287*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20015231015228943513 20000000000000000000 10001881512063869 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001881512063869/10000000000000000 : ℝ)) (X := (20015231015228943513/20000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014133647151184541/10000000000000000000 : ℝ) ≤ (400139673531819/400000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (10014133647151184541/10000000000000000000 : ℝ)^2048 ≤ (400139673531819/400000000000000 : ℝ)^8287 := by
      have hnat : (10014133647151184541 : ℕ)^2048*400000000000000^8287 ≤ 400139673531819^8287*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014133647151184541 10000000000000000000 400139673531819 400000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400139673531819/400000000000000 : ℝ)) (X := (10014133647151184541/10000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(274342019439743/5000000000000000000 : ℝ) ≤ ((77923604677958137461/77950000000000000000 : ℝ)+2*(805163115803/389750000000000 : ℝ)*(2213/25000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (77923604677958137461/77950000000000000000 : ℝ)+2*(805163115803/389750000000000 : ℝ)*(2213/25000 : ℝ)=(10000271185832263/10000000000000000 : ℝ) by norm_num, show 1+2*(274342019439743/5000000000000000000 : ℝ)=(2500274342019439743/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14133647151184541/20000000000000000000 : ℝ)+(274342019439743/5000000000000000000 : ℝ) ≤ ((77923604677958137461/77950000000000000000 : ℝ)+(805163115803/389750000000000 : ℝ)*((16647/100000 : ℝ)+(2213/25000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (77923604677958137461/77950000000000000000 : ℝ)+(805163115803/389750000000000 : ℝ)*((16647/100000 : ℝ)+(2213/25000 : ℝ))=(10001881512063869/10000000000000000 : ℝ) by norm_num, show 1+(14133647151184541/20000000000000000000 : ℝ)+(274342019439743/5000000000000000000 : ℝ)=(20015231015228943513/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14133647151184541/20000000000000000000 : ℝ) ≤ ((77923604677958137461/77950000000000000000 : ℝ)+2*(805163115803/389750000000000 : ℝ)*(16647/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (77923604677958137461/77950000000000000000 : ℝ)+2*(805163115803/389750000000000 : ℝ)*(16647/100000 : ℝ)=(400139673531819/400000000000000 : ℝ) by norm_num, show 1+2*(14133647151184541/20000000000000000000 : ℝ)=(10014133647151184541/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77923604677958137461/77950000000000000000 : ℝ)*(X 1 0+X 2 0)+(805163115803/389750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (16647/100000 : ℝ)) (c := (77923604677958137461/77950000000000000000 : ℝ)) (alpha := (805163115803/389750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77923604677958137461/77950000000000000000 : ℝ)*(X 0 1+X 2 1)+(805163115803/389750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (16647/100000 : ℝ)) (c := (77923604677958137461/77950000000000000000 : ℝ)) (alpha := (805163115803/389750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77923604677958137461/77950000000000000000 : ℝ)*(X 0 2+X 1 2)+(805163115803/389750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2213/25000 : ℝ)) (hi := (16647/100000 : ℝ)) (c := (77923604677958137461/77950000000000000000 : ℝ)) (alpha := (805163115803/389750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185209793/10000000000 : ℝ)*X 0 0+(5434221881/10000000000 : ℝ)*X 0 1+(1045490039/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677475597/5000000000 : ℝ)*X 1 0+(-2291018331/10000000000 : ℝ)*X 1 1+(5227450057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354951063/10000000000 : ℝ)*X 2 0+(5227450507/10000000000 : ℝ)*X 2 1+(-458203583/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184378421/5000000000 : ℝ)*X 0 0+(2084871537/5000000000 : ℝ)*X 0 1+(143041261/312500000 : ℝ)*X 0 2+(2184378421/5000000000 : ℝ)*X 1 0+(2084871537/5000000000 : ℝ)*X 1 1+(143041261/312500000 : ℝ)*X 1 2+(2184378421/5000000000 : ℝ)*X 2 0+(2084871537/5000000000 : ℝ)*X 2 1+(143041261/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546307619/2500000000 : ℝ)*X 0 0+(5228279977/10000000000 : ℝ)*X 0 1+(5433387217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265137477/500000000 : ℝ)*X 1 0+(-1042540527/5000000000 : ℝ)*X 1 1+(135834687/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165710927/312500000 : ℝ)*X 2 0+(135834681/250000000 : ℝ)*X 2 1+(-1042540607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368797181/10000000000 : ℝ)*X 0 0+(4575685491/10000000000 : ℝ)*X 0 1+(2085693791/5000000000 : ℝ)*X 0 2+(4368797181/10000000000 : ℝ)*X 1 0+(4575685491/10000000000 : ℝ)*X 1 1+(2085693791/5000000000 : ℝ)*X 1 2+(4368797181/10000000000 : ℝ)*X 2 0+(4575685491/10000000000 : ℝ)*X 2 1+(2085693791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341316084902423319287289/38975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2214991821/100000000000000 : ℝ)*(base19) + (834536061/50000000000000 : ℝ)*(base23) + (228981447/100000000000000 : ℝ)*(lower2) + (1417399/1000000000000 : ℝ)*(upper3) + (205902291/100000000000000 : ℝ)*(upper5) + (1822471551939099/50000000000000 : ℝ)*(major0) + (1822471551939099/50000000000000 : ℝ)*(major1) + (1822471551939099/50000000000000 : ℝ)*(major2) + (2418143897726427/50000000000000 : ℝ)*(sp0) + (2418163394458461/50000000000000 : ℝ)*(sp1) + (4836327334836621/100000000000000 : ℝ)*(sp2) + (490707892402321/20000000000000 : ℝ)*(sp3) + (2575528493/6250000000000 : ℝ)*(sp4) + (4362481443/25000000000000 : ℝ)*(sp7) + (2453556911937377/100000000000000 : ℝ)*(f.failure) + (2418164501954371/50000000000000 : ℝ)*(f.sum) + (26904611208447/9743750000000000000000000000 : ℝ)*base65 + (5658731731628112361/3897500000000000000000000000000000 : ℝ)*base68 + (12044735512466887639/3897500000000000000000000000000000 : ℝ)*base69 + (2043881000766887639/3897500000000000000000000000000000 : ℝ)*base71 + (42037217942003/9743750000000000000000000000 : ℝ)*base74 + (7263379430913112361/3897500000000000000000000000000000 : ℝ)*base76 + (28840856739404387639/3897500000000000000000000000000000 : ℝ)*base77 + (42216361520185612361/3897500000000000000000000000000000 : ℝ)*base80 + (19051272408787/38975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3365753/1250000000000000000000 : ℝ)*base89 + (3365753/1250000000000000000000 : ℝ)*base91 + (3365753/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67425914358859010894451/19487500000000000000000000000 : ℝ) := by norm_num
    linear_combination (149599201/25000000000000 : ℝ)*(base19) + (449236713/50000000000000 : ℝ)*(base23) + (16243411/12500000000000 : ℝ)*(upper3) + (42657789/50000000000000 : ℝ)*(lower4) + (918614922113259/25000000000000 : ℝ)*(major0) + (918614922113259/25000000000000 : ℝ)*(major1) + (918614922113259/25000000000000 : ℝ)*(major2) + (6592848027/50000000000000 : ℝ)*(sp1) + (7871718627/50000000000000 : ℝ)*(sp2) + (273722059/100000000000000 : ℝ)*(sp3) + (609436694577107/12500000000000 : ℝ)*(sp4) + (4875479772523999/100000000000000 : ℝ)*(sp5) + (4875476914706177/100000000000000 : ℝ)*(sp6) + (154589089452203/6250000000000 : ℝ)*(sp7) + (2473425704957307/100000000000000 : ℝ)*(f.failure) + (609436694577107/12500000000000 : ℝ)*(f.sum) + (35414826659283/19487500000000000000000000000 : ℝ)*base65 + (1079879865985595399/1948750000000000000000000000000000 : ℝ)*base67 + (8143780738001904601/1948750000000000000000000000000000 : ℝ)*base70 + (17940729786855595399/1948750000000000000000000000000000 : ℝ)*base71 + (1745002246333/19487500000000000000000000000 : ℝ)*base73 + (12189342565394404601/1948750000000000000000000000000000 : ℝ)*base76 + (4490502899298095399/1948750000000000000000000000000000 : ℝ)*base77 + (2272899582531904601/1948750000000000000000000000000000 : ℝ)*base80 + (8727724399723/4871875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (732477/1250000000000000000000 : ℝ)*base90 + (732477/1250000000000000000000 : ℝ)*base92 + (732477/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2973/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s4_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094308373/5000000000 : ℝ)*x 0 + (2702124377/5000000000 : ℝ)*x 1 + (1051039247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094308373/5000000000 : ℝ)^259 ≤ (13292603040301/100000000000000 : ℝ)^195 := by
    have hnat : (1094308373 : ℕ)^259*100000000000000^195 ≤ 13292603040301^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094308373 5000000000 13292603040301 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702124377/5000000000 : ℝ)^259 ≤ (22079422018493/50000000000000 : ℝ)^195 := by
    have hnat : (2702124377 : ℕ)^259*50000000000000^195 ≤ 22079422018493^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702124377 5000000000 22079422018493 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051039247/2000000000 : ℝ)^259 ≤ (5318569114013/12500000000000 : ℝ)^195 := by
    have hnat : (1051039247 : ℕ)^259*12500000000000^195 ≤ 5318569114013^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051039247 2000000000 5318569114013 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094308373/5000000000 : ℝ), (2702124377/5000000000 : ℝ), (1051039247/2000000000 : ℝ)] ![(13292603040301/100000000000000 : ℝ), (22079422018493/50000000000000 : ℝ), (5318569114013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094308373/5000000000 : ℝ)|^259 ≤ (13292603040301/100000000000000 : ℝ)^195
        have hw : |(-1094308373/5000000000 : ℝ)|=(1094308373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702124377/5000000000 : ℝ)|^259 ≤ (22079422018493/50000000000000 : ℝ)^195
        have hw : |(2702124377/5000000000 : ℝ)|=(2702124377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051039247/2000000000 : ℝ)|^259 ≤ (5318569114013/12500000000000 : ℝ)^195
        have hw : |(1051039247/2000000000 : ℝ)|=(1051039247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2673751149/5000000000 : ℝ)*x 0 + (-28305027/125000000 : ℝ)*x 1 + (5255196539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673751149/5000000000 : ℝ)^259 ≤ (10886010429007/25000000000000 : ℝ)^195 := by
    have hnat : (2673751149 : ℕ)^259*25000000000000^195 ≤ 10886010429007^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673751149 5000000000 10886010429007 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28305027/125000000 : ℝ)^259 ≤ (13907402089121/100000000000000 : ℝ)^195 := by
    have hnat : (28305027 : ℕ)^259*100000000000000^195 ≤ 13907402089121^195*125000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28305027 125000000 13907402089121 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255196539/10000000000 : ℝ)^259 ≤ (10637139045313/25000000000000 : ℝ)^195 := by
    have hnat : (5255196539 : ℕ)^259*25000000000000^195 ≤ 10637139045313^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255196539 10000000000 10637139045313 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673751149/5000000000 : ℝ), (-28305027/125000000 : ℝ), (5255196539/10000000000 : ℝ)] ![(10886010429007/25000000000000 : ℝ), (13907402089121/100000000000000 : ℝ), (10637139045313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673751149/5000000000 : ℝ)|^259 ≤ (10886010429007/25000000000000 : ℝ)^195
        have hw : |(2673751149/5000000000 : ℝ)|=(2673751149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28305027/125000000 : ℝ)|^259 ≤ (13907402089121/100000000000000 : ℝ)^195
        have hw : |(-28305027/125000000 : ℝ)|=(28305027/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255196539/10000000000 : ℝ)|^259 ≤ (10637139045313/25000000000000 : ℝ)^195
        have hw : |(5255196539/10000000000 : ℝ)|=(5255196539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2673751163/5000000000 : ℝ)*x 0 + (5255196487/10000000000 : ℝ)*x 1 + (-2264402191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673751163/5000000000 : ℝ)^259 ≤ (2177202100943/5000000000000 : ℝ)^195 := by
    have hnat : (2673751163 : ℕ)^259*5000000000000^195 ≤ 2177202100943^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673751163 5000000000 2177202100943 5000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255196487/10000000000 : ℝ)^259 ≤ (5318569452757/12500000000000 : ℝ)^195 := by
    have hnat : (5255196487 : ℕ)^259*12500000000000^195 ≤ 5318569452757^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255196487 10000000000 5318569452757 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264402191/10000000000 : ℝ)^259 ≤ (3476850585501/25000000000000 : ℝ)^195 := by
    have hnat : (2264402191 : ℕ)^259*25000000000000^195 ≤ 3476850585501^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264402191 10000000000 3476850585501 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673751163/5000000000 : ℝ), (5255196487/10000000000 : ℝ), (-2264402191/10000000000 : ℝ)] ![(2177202100943/5000000000000 : ℝ), (5318569452757/12500000000000 : ℝ), (3476850585501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673751163/5000000000 : ℝ)|^259 ≤ (2177202100943/5000000000000 : ℝ)^195
        have hw : |(2673751163/5000000000 : ℝ)|=(2673751163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255196487/10000000000 : ℝ)|^259 ≤ (5318569452757/12500000000000 : ℝ)^195
        have hw : |(5255196487/10000000000 : ℝ)|=(5255196487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2264402191/10000000000 : ℝ)|^259 ≤ (3476850585501/25000000000000 : ℝ)^195
        have hw : |(-2264402191/10000000000 : ℝ)|=(2264402191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (437078437/1000000000 : ℝ)*x 0 + (2113182349/5000000000 : ℝ)*x 1 + (2260084623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437078437/1000000000 : ℝ)^259 ≤ (1040972241321/3125000000000 : ℝ)^195 := by
    have hnat : (437078437 : ℕ)^259*3125000000000^195 ≤ 1040972241321^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437078437 1000000000 1040972241321 3125000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113182349/5000000000 : ℝ)^259 ≤ (31857186030077/100000000000000 : ℝ)^195 := by
    have hnat : (2113182349 : ℕ)^259*100000000000000^195 ≤ 31857186030077^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113182349 5000000000 31857186030077 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260084623/5000000000 : ℝ)^259 ≤ (34831702228023/100000000000000 : ℝ)^195 := by
    have hnat : (2260084623 : ℕ)^259*100000000000000^195 ≤ 34831702228023^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260084623 5000000000 34831702228023 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437078437/1000000000 : ℝ), (2113182349/5000000000 : ℝ), (2260084623/5000000000 : ℝ)] ![(1040972241321/3125000000000 : ℝ), (31857186030077/100000000000000 : ℝ), (34831702228023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437078437/1000000000 : ℝ)|^259 ≤ (1040972241321/3125000000000 : ℝ)^195
        have hw : |(437078437/1000000000 : ℝ)|=(437078437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113182349/5000000000 : ℝ)|^259 ≤ (31857186030077/100000000000000 : ℝ)^195
        have hw : |(2113182349/5000000000 : ℝ)|=(2113182349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260084623/5000000000 : ℝ)|^259 ≤ (34831702228023/100000000000000 : ℝ)^195
        have hw : |(2260084623/5000000000 : ℝ)|=(2260084623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094312189/5000000000 : ℝ)*x 0 + (2627814169/5000000000 : ℝ)*x 1 + (2701907457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094312189/5000000000 : ℝ)^259 ≤ (13292664606747/100000000000000 : ℝ)^195 := by
    have hnat : (1094312189 : ℕ)^259*100000000000000^195 ≤ 13292664606747^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094312189 5000000000 13292664606747 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627814169/5000000000 : ℝ)^259 ≤ (21276599856961/50000000000000 : ℝ)^195 := by
    have hnat : (2627814169 : ℕ)^259*50000000000000^195 ≤ 21276599856961^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627814169 5000000000 21276599856961 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701907457/5000000000 : ℝ)^259 ≤ (44154135658271/100000000000000 : ℝ)^195 := by
    have hnat : (2701907457 : ℕ)^259*100000000000000^195 ≤ 44154135658271^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701907457 5000000000 44154135658271 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094312189/5000000000 : ℝ), (2627814169/5000000000 : ℝ), (2701907457/5000000000 : ℝ)] ![(13292664606747/100000000000000 : ℝ), (21276599856961/50000000000000 : ℝ), (44154135658271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094312189/5000000000 : ℝ)|^259 ≤ (13292664606747/100000000000000 : ℝ)^195
        have hw : |(-1094312189/5000000000 : ℝ)|=(1094312189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627814169/5000000000 : ℝ)|^259 ≤ (21276599856961/50000000000000 : ℝ)^195
        have hw : |(2627814169/5000000000 : ℝ)|=(2627814169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701907457/5000000000 : ℝ)|^259 ≤ (44154135658271/100000000000000 : ℝ)^195
        have hw : |(2701907457/5000000000 : ℝ)|=(2701907457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5309875497/10000000000 : ℝ)*x 0 + (-2115783513/10000000000 : ℝ)*x 1 + (1350953777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309875497/10000000000 : ℝ)^259 ≤ (21568781573783/50000000000000 : ℝ)^195 := by
    have hnat : (5309875497 : ℕ)^259*50000000000000^195 ≤ 21568781573783^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309875497 10000000000 21568781573783 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115783513/10000000000 : ℝ)^259 ≤ (12708299070313/100000000000000 : ℝ)^195 := by
    have hnat : (2115783513 : ℕ)^259*100000000000000^195 ≤ 12708299070313^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115783513 10000000000 12708299070313 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350953777/2500000000 : ℝ)^259 ≤ (22077068881843/50000000000000 : ℝ)^195 := by
    have hnat : (1350953777 : ℕ)^259*50000000000000^195 ≤ 22077068881843^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350953777 2500000000 22077068881843 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309875497/10000000000 : ℝ), (-2115783513/10000000000 : ℝ), (1350953777/2500000000 : ℝ)] ![(21568781573783/50000000000000 : ℝ), (12708299070313/100000000000000 : ℝ), (22077068881843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309875497/10000000000 : ℝ)|^259 ≤ (21568781573783/50000000000000 : ℝ)^195
        have hw : |(5309875497/10000000000 : ℝ)|=(5309875497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115783513/10000000000 : ℝ)|^259 ≤ (12708299070313/100000000000000 : ℝ)^195
        have hw : |(-2115783513/10000000000 : ℝ)|=(2115783513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350953777/2500000000 : ℝ)|^259 ≤ (22077068881843/50000000000000 : ℝ)^195
        have hw : |(1350953777/2500000000 : ℝ)|=(1350953777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1327468839/2500000000 : ℝ)*x 0 + (1080763029/2000000000 : ℝ)*x 1 + (-1057891827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327468839/2500000000 : ℝ)^259 ≤ (10784390406531/25000000000000 : ℝ)^195 := by
    have hnat : (1327468839 : ℕ)^259*25000000000000^195 ≤ 10784390406531^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327468839 2500000000 10784390406531 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080763029/2000000000 : ℝ)^259 ≤ (8830827633047/20000000000000 : ℝ)^195 := by
    have hnat : (1080763029 : ℕ)^259*20000000000000^195 ≤ 8830827633047^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080763029 2000000000 8830827633047 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057891827/5000000000 : ℝ)^259 ≤ (6354150097589/50000000000000 : ℝ)^195 := by
    have hnat : (1057891827 : ℕ)^259*50000000000000^195 ≤ 6354150097589^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057891827 5000000000 6354150097589 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327468839/2500000000 : ℝ), (1080763029/2000000000 : ℝ), (-1057891827/5000000000 : ℝ)] ![(10784390406531/25000000000000 : ℝ), (8830827633047/20000000000000 : ℝ), (6354150097589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327468839/2500000000 : ℝ)|^259 ≤ (10784390406531/25000000000000 : ℝ)^195
        have hw : |(1327468839/2500000000 : ℝ)|=(1327468839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080763029/2000000000 : ℝ)|^259 ≤ (8830827633047/20000000000000 : ℝ)^195
        have hw : |(1080763029/2000000000 : ℝ)|=(1080763029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057891827/5000000000 : ℝ)|^259 ≤ (6354150097589/50000000000000 : ℝ)^195
        have hw : |(-1057891827/5000000000 : ℝ)|=(1057891827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s4_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (874159863/2000000000 : ℝ)*x 0 + (2259658953/5000000000 : ℝ)*x 1 + (4227219859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874159863/2000000000 : ℝ)^259 ≤ (33311263005597/100000000000000 : ℝ)^195 := by
    have hnat : (874159863 : ℕ)^259*100000000000000^195 ≤ 33311263005597^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874159863 2000000000 33311263005597 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259658953/5000000000 : ℝ)^259 ≤ (8705747271611/25000000000000 : ℝ)^195 := by
    have hnat : (2259658953 : ℕ)^259*25000000000000^195 ≤ 8705747271611^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259658953 5000000000 8705747271611 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227219859/10000000000 : ℝ)^259 ≤ (31865747885703/100000000000000 : ℝ)^195 := by
    have hnat : (4227219859 : ℕ)^259*100000000000000^195 ≤ 31865747885703^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227219859 10000000000 31865747885703 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874159863/2000000000 : ℝ), (2259658953/5000000000 : ℝ), (4227219859/10000000000 : ℝ)] ![(33311263005597/100000000000000 : ℝ), (8705747271611/25000000000000 : ℝ), (31865747885703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874159863/2000000000 : ℝ)|^259 ≤ (33311263005597/100000000000000 : ℝ)^195
        have hw : |(874159863/2000000000 : ℝ)|=(874159863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259658953/5000000000 : ℝ)|^259 ≤ (8705747271611/25000000000000 : ℝ)^195
        have hw : |(2259658953/5000000000 : ℝ)|=(2259658953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227219859/10000000000 : ℝ)|^259 ≤ (31865747885703/100000000000000 : ℝ)^195
        have hw : |(4227219859/10000000000 : ℝ)|=(4227219859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1049/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2973/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1049/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1049/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2973/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1049/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1049/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2973/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1049/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1049/10000 : ℝ) ^ (8287/2048 : ℝ) ≤ (10906337696272211/100000000000000000000 : ℝ) := by
    have hpowers : (1049/10000 : ℝ)^8287 ≤ (10906337696272211/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1049 : ℕ)^8287*100000000000000000000^2048 ≤ 10906337696272211^2048*10000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1049 10000 10906337696272211 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1049/10000 : ℝ)) (X := (10906337696272211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2973/20000 : ℝ) ^ (8287/2048 : ℝ) ≤ (5586877048287951/12500000000000000000 : ℝ) := by
    have hpowers : (2973/20000 : ℝ)^8287 ≤ (5586877048287951/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2973 : ℕ)^8287*12500000000000000000^2048 ≤ 5586877048287951^2048*20000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2973 20000 5586877048287951 12500000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2973/20000 : ℝ)) (X := (5586877048287951/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010906337696272211/50000000000000000000 : ℝ) ≤ (5000269510628813/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50010906337696272211/50000000000000000000 : ℝ)^2048 ≤ (5000269510628813/5000000000000000 : ℝ)^8287 := by
      have hnat : (50010906337696272211 : ℕ)^2048*5000000000000000^8287 ≤ 5000269510628813^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010906337696272211 50000000000000000000 5000269510628813 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269510628813/5000000000000000 : ℝ)) (X := (50010906337696272211/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055601354082575819/100000000000000000000 : ℝ) ≤ (625085863209977/625000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (100055601354082575819/100000000000000000000 : ℝ)^2048 ≤ (625085863209977/625000000000000 : ℝ)^8287 := by
      have hnat : (100055601354082575819 : ℕ)^2048*625000000000000^8287 ≤ 625085863209977^8287*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055601354082575819 100000000000000000000 625085863209977 625000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625085863209977/625000000000000 : ℝ)) (X := (100055601354082575819/100000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6255586877048287951/6250000000000000000 : ℝ) ≤ (5001104300730819/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (6255586877048287951/6250000000000000000 : ℝ)^2048 ≤ (5001104300730819/5000000000000000 : ℝ)^8287 := by
      have hnat : (6255586877048287951 : ℕ)^2048*5000000000000000^8287 ≤ 5001104300730819^8287*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255586877048287951 6250000000000000000 5001104300730819 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001104300730819/5000000000000000 : ℝ)) (X := (6255586877048287951/6250000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10906337696272211/100000000000000000000 : ℝ) ≤ ((624783490309457541/625000000000000000 : ℝ)+2*(59627864429/31250000000000 : ℝ)*(1049/10000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (624783490309457541/625000000000000000 : ℝ)+2*(59627864429/31250000000000 : ℝ)*(1049/10000 : ℝ)=(5000269510628813/5000000000000000 : ℝ) by norm_num, show 1+2*(10906337696272211/100000000000000000000 : ℝ)=(50010906337696272211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5586877048287951/12500000000000000000 : ℝ)+(10906337696272211/100000000000000000000 : ℝ) ≤ ((624783490309457541/625000000000000000 : ℝ)+(59627864429/31250000000000 : ℝ)*((2973/20000 : ℝ)+(1049/10000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (624783490309457541/625000000000000000 : ℝ)+(59627864429/31250000000000 : ℝ)*((2973/20000 : ℝ)+(1049/10000 : ℝ))=(625085863209977/625000000000000 : ℝ) by norm_num, show 1+(5586877048287951/12500000000000000000 : ℝ)+(10906337696272211/100000000000000000000 : ℝ)=(100055601354082575819/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5586877048287951/12500000000000000000 : ℝ) ≤ ((624783490309457541/625000000000000000 : ℝ)+2*(59627864429/31250000000000 : ℝ)*(2973/20000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (624783490309457541/625000000000000000 : ℝ)+2*(59627864429/31250000000000 : ℝ)*(2973/20000 : ℝ)=(5001104300730819/5000000000000000 : ℝ) by norm_num, show 1+2*(5586877048287951/12500000000000000000 : ℝ)=(6255586877048287951/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (624783490309457541/625000000000000000 : ℝ)*(X 1 0+X 2 0)+(59627864429/31250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (2973/20000 : ℝ)) (c := (624783490309457541/625000000000000000 : ℝ)) (alpha := (59627864429/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (624783490309457541/625000000000000000 : ℝ)*(X 0 1+X 2 1)+(59627864429/31250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (2973/20000 : ℝ)) (c := (624783490309457541/625000000000000000 : ℝ)) (alpha := (59627864429/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (624783490309457541/625000000000000000 : ℝ)*(X 0 2+X 1 2)+(59627864429/31250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (2973/20000 : ℝ)) (c := (624783490309457541/625000000000000000 : ℝ)) (alpha := (59627864429/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094308373/5000000000 : ℝ)*X 0 0+(2702124377/5000000000 : ℝ)*X 0 1+(1051039247/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673751149/5000000000 : ℝ)*X 1 0+(-28305027/125000000 : ℝ)*X 1 1+(5255196539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673751163/5000000000 : ℝ)*X 2 0+(5255196487/10000000000 : ℝ)*X 2 1+(-2264402191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437078437/1000000000 : ℝ)*X 0 0+(2113182349/5000000000 : ℝ)*X 0 1+(2260084623/5000000000 : ℝ)*X 0 2+(437078437/1000000000 : ℝ)*X 1 0+(2113182349/5000000000 : ℝ)*X 1 1+(2260084623/5000000000 : ℝ)*X 1 2+(437078437/1000000000 : ℝ)*X 2 0+(2113182349/5000000000 : ℝ)*X 2 1+(2260084623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094312189/5000000000 : ℝ)*X 0 0+(2627814169/5000000000 : ℝ)*X 0 1+(2701907457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309875497/10000000000 : ℝ)*X 1 0+(-2115783513/10000000000 : ℝ)*X 1 1+(1350953777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327468839/2500000000 : ℝ)*X 2 0+(1080763029/2000000000 : ℝ)*X 2 1+(-1057891827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874159863/2000000000 : ℝ)*X 0 0+(2259658953/5000000000 : ℝ)*X 0 1+(4227219859/10000000000 : ℝ)*X 0 2+(874159863/2000000000 : ℝ)*X 1 0+(2259658953/5000000000 : ℝ)*X 1 1+(4227219859/10000000000 : ℝ)*X 1 2+(874159863/2000000000 : ℝ)*X 2 0+(2259658953/5000000000 : ℝ)*X 2 1+(4227219859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1524916698585211353628689/781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (594366359/50000000000000 : ℝ)*(base19) + (4078847/390625000000 : ℝ)*(base23) + (263381619/100000000000000 : ℝ)*(upper3) + (4804127/5000000000000 : ℝ)*(upper4) + (47871243/50000000000000 : ℝ)*(upper5) + (126409654574593/2500000000000 : ℝ)*(major0) + (126409654574593/2500000000000 : ℝ)*(major1) + (126409654574593/2500000000000 : ℝ)*(major2) + (1677270669027011/25000000000000 : ℝ)*(sp0) + (6709115440431677/100000000000000 : ℝ)*(sp1) + (6709115584979563/100000000000000 : ℝ)*(sp2) + (1701818741118141/50000000000000 : ℝ)*(sp3) + (679061127/2000000000000 : ℝ)*(sp4) + (18189503643/100000000000000 : ℝ)*(sp7) + (1701827835869963/50000000000000 : ℝ)*(f.failure) + (3354558314582197/50000000000000 : ℝ)*(f.sum) + (2811295212273/625000000000000000000000000 : ℝ)*base66 + (5683338951920813/1562500000000000000000000000000 : ℝ)*base67 + (1354504921516687/1562500000000000000000000000000 : ℝ)*base70 + (13083821612141687/1562500000000000000000000000000 : ℝ)*base72 + (175950828949/312500000000000000000000000 : ℝ)*base74 + (5013798144954187/1562500000000000000000000000000 : ℝ)*base76 + (4204506837858313/1562500000000000000000000000000 : ℝ)*base77 + (13562241837141687/1562500000000000000000000000000 : ℝ)*base80 + (77294355831/78125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7351507/625000000000000000000 : ℝ)*base89 + (7351507/625000000000000000000 : ℝ)*base91 + (7351507/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5429912594889212077941/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1691534749/100000000000000 : ℝ)*(base19) + (833046007/50000000000000 : ℝ)*(base23) + (94092447/100000000000000 : ℝ)*(upper2) + (206297907/100000000000000 : ℝ)*(upper3) + (50730587/25000000000000 : ℝ)*(upper5) + (5085875864649439/100000000000000 : ℝ)*(major0) + (5085875864649439/100000000000000 : ℝ)*(major1) + (5085875864649439/100000000000000 : ℝ)*(major2) + (47240307787/100000000000000 : ℝ)*(sp1) + (43930769899/100000000000000 : ℝ)*(sp2) + (6748245142286333/100000000000000 : ℝ)*(sp4) + (6748196210443797/100000000000000 : ℝ)*(sp5) + (6748199545424421/100000000000000 : ℝ)*(sp6) + (855876588834067/25000000000000 : ℝ)*(sp7) + (855876588834067/25000000000000 : ℝ)*(f.failure) + (6748245142286333/100000000000000 : ℝ)*(f.sum) + (3259028661397/781250000000000000000000000 : ℝ)*base66 + (860193872201589499/62500000000000000000000000000000 : ℝ)*base67 + (16019046451589499/62500000000000000000000000000000 : ℝ)*base69 + (510885733610910501/62500000000000000000000000000000 : ℝ)*base72 + (21772493226287/3125000000000000000000000000 : ℝ)*base73 + (160659947735910501/62500000000000000000000000000000 : ℝ)*base76 + (580011815798410501/62500000000000000000000000000000 : ℝ)*base78 + (94075353201589499/62500000000000000000000000000000 : ℝ)*base79 + (15254970907537/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (79837/312500000000000000000 : ℝ)*base90 + (79837/312500000000000000000 : ℝ)*base92 + (79837/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2973/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s5_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189363209/10000000000 : ℝ)*x 0 + (107923591/200000000 : ℝ)*x 1 + (5262776073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189363209/10000000000 : ℝ)^259 ≤ (13298625003/100000000000 : ℝ)^195 := by
    have hnat : (2189363209 : ℕ)^259*100000000000^195 ≤ 13298625003^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189363209 10000000000 13298625003 100000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107923591/200000000 : ℝ)^259 ≤ (44071290891949/100000000000000 : ℝ)^195 := by
    have hnat : (107923591 : ℕ)^259*100000000000000^195 ≤ 44071290891949^195*200000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107923591 200000000 44071290891949 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262776073/10000000000 : ℝ)^259 ≤ (42630084083547/100000000000000 : ℝ)^195 := by
    have hnat : (5262776073 : ℕ)^259*100000000000000^195 ≤ 42630084083547^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262776073 10000000000 42630084083547 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189363209/10000000000 : ℝ), (107923591/200000000 : ℝ), (5262776073/10000000000 : ℝ)] ![(13298625003/100000000000 : ℝ), (44071290891949/100000000000000 : ℝ), (42630084083547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189363209/10000000000 : ℝ)|^259 ≤ (13298625003/100000000000 : ℝ)^195
        have hw : |(-2189363209/10000000000 : ℝ)|=(2189363209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107923591/200000000 : ℝ)|^259 ≤ (44071290891949/100000000000000 : ℝ)^195
        have hw : |(107923591/200000000 : ℝ)|=(107923591/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262776073/10000000000 : ℝ)|^259 ≤ (42630084083547/100000000000000 : ℝ)^195
        have hw : |(5262776073/10000000000 : ℝ)|=(5262776073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5345487849/10000000000 : ℝ)*x 0 + (-564268383/2500000000 : ℝ)*x 1 + (1315694237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345487849/10000000000 : ℝ)^259 ≤ (21761127987511/50000000000000 : ℝ)^195 := by
    have hnat : (5345487849 : ℕ)^259*50000000000000^195 ≤ 21761127987511^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345487849 10000000000 21761127987511 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564268383/2500000000 : ℝ)^259 ≤ (1384765050909/10000000000000 : ℝ)^195 := by
    have hnat : (564268383 : ℕ)^259*10000000000000^195 ≤ 1384765050909^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564268383 2500000000 1384765050909 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315694237/2500000000 : ℝ)^259 ≤ (21315046748777/50000000000000 : ℝ)^195 := by
    have hnat : (1315694237 : ℕ)^259*50000000000000^195 ≤ 21315046748777^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315694237 2500000000 21315046748777 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345487849/10000000000 : ℝ), (-564268383/2500000000 : ℝ), (1315694237/2500000000 : ℝ)] ![(21761127987511/50000000000000 : ℝ), (1384765050909/10000000000000 : ℝ), (21315046748777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345487849/10000000000 : ℝ)|^259 ≤ (21761127987511/50000000000000 : ℝ)^195
        have hw : |(5345487849/10000000000 : ℝ)|=(5345487849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564268383/2500000000 : ℝ)|^259 ≤ (1384765050909/10000000000000 : ℝ)^195
        have hw : |(-564268383/2500000000 : ℝ)|=(564268383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315694237/2500000000 : ℝ)|^259 ≤ (21315046748777/50000000000000 : ℝ)^195
        have hw : |(1315694237/2500000000 : ℝ)|=(1315694237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069097621/2000000000 : ℝ)*x 0 + (41115441/78125000 : ℝ)*x 1 + (-2257073853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069097621/2000000000 : ℝ)^259 ≤ (340017646433/781250000000 : ℝ)^195 := by
    have hnat : (1069097621 : ℕ)^259*781250000000^195 ≤ 340017646433^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069097621 2000000000 340017646433 781250000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41115441/78125000 : ℝ)^259 ≤ (42630088118121/100000000000000 : ℝ)^195 := by
    have hnat : (41115441 : ℕ)^259*100000000000000^195 ≤ 42630088118121^195*78125000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41115441 78125000 42630088118121 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257073853/10000000000 : ℝ)^259 ≤ (6923826562433/50000000000000 : ℝ)^195 := by
    have hnat : (2257073853 : ℕ)^259*50000000000000^195 ≤ 6923826562433^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257073853 10000000000 6923826562433 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069097621/2000000000 : ℝ), (41115441/78125000 : ℝ), (-2257073853/10000000000 : ℝ)] ![(340017646433/781250000000 : ℝ), (42630088118121/100000000000000 : ℝ), (6923826562433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069097621/2000000000 : ℝ)|^259 ≤ (340017646433/781250000000 : ℝ)^195
        have hw : |(1069097621/2000000000 : ℝ)|=(1069097621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41115441/78125000 : ℝ)|^259 ≤ (42630088118121/100000000000000 : ℝ)^195
        have hw : |(41115441/78125000 : ℝ)|=(41115441/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257073853/10000000000 : ℝ)|^259 ≤ (6923826562433/50000000000000 : ℝ)^195
        have hw : |(-2257073853/10000000000 : ℝ)|=(2257073853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (174848843/400000000 : ℝ)*x 0 + (1060432803/2500000000 : ℝ)*x 1 + (2252344191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174848843/400000000 : ℝ)^259 ≤ (8328883103379/25000000000000 : ℝ)^195 := by
    have hnat : (174848843 : ℕ)^259*25000000000000^195 ≤ 8328883103379^195*400000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174848843 400000000 8328883103379 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060432803/2500000000 : ℝ)^259 ≤ (16005560942253/50000000000000 : ℝ)^195 := by
    have hnat : (1060432803 : ℕ)^259*50000000000000^195 ≤ 16005560942253^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060432803 2500000000 16005560942253 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252344191/5000000000 : ℝ)^259 ≤ (34673345685781/100000000000000 : ℝ)^195 := by
    have hnat : (2252344191 : ℕ)^259*100000000000000^195 ≤ 34673345685781^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252344191 5000000000 34673345685781 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174848843/400000000 : ℝ), (1060432803/2500000000 : ℝ), (2252344191/5000000000 : ℝ)] ![(8328883103379/25000000000000 : ℝ), (16005560942253/50000000000000 : ℝ), (34673345685781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174848843/400000000 : ℝ)|^259 ≤ (8328883103379/25000000000000 : ℝ)^195
        have hw : |(174848843/400000000 : ℝ)|=(174848843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060432803/2500000000 : ℝ)|^259 ≤ (16005560942253/50000000000000 : ℝ)^195
        have hw : |(1060432803/2500000000 : ℝ)|=(1060432803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252344191/5000000000 : ℝ)|^259 ≤ (34673345685781/100000000000000 : ℝ)^195
        have hw : |(2252344191/5000000000 : ℝ)|=(2252344191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-109468423/500000000 : ℝ)*x 0 + (1052624531/2000000000 : ℝ)*x 1 + (1348957973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109468423/500000000 : ℝ)^259 ≤ (13298667366933/100000000000000 : ℝ)^195 := by
    have hnat : (109468423 : ℕ)^259*100000000000000^195 ≤ 13298667366933^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109468423 500000000 13298667366933 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052624531/2000000000 : ℝ)^259 ≤ (5329226619091/12500000000000 : ℝ)^195 := by
    have hnat : (1052624531 : ℕ)^259*12500000000000^195 ≤ 5329226619091^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052624531 2000000000 5329226619091 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348957973/2500000000 : ℝ)^259 ≤ (1377109989667/3125000000000 : ℝ)^195 := by
    have hnat : (1348957973 : ℕ)^259*3125000000000^195 ≤ 1377109989667^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348957973 2500000000 1377109989667 3125000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109468423/500000000 : ℝ), (1052624531/2000000000 : ℝ), (1348957973/2500000000 : ℝ)] ![(13298667366933/100000000000000 : ℝ), (5329226619091/12500000000000 : ℝ), (1377109989667/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109468423/500000000 : ℝ)|^259 ≤ (13298667366933/100000000000000 : ℝ)^195
        have hw : |(-109468423/500000000 : ℝ)|=(109468423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052624531/2000000000 : ℝ)|^259 ≤ (5329226619091/12500000000000 : ℝ)^195
        have hw : |(1052624531/2000000000 : ℝ)|=(1052624531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348957973/2500000000 : ℝ)|^259 ≤ (1377109989667/3125000000000 : ℝ)^195
        have hw : |(1348957973/2500000000 : ℝ)|=(1348957973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1037463/1953125 : ℝ)*x 0 + (-424803681/2000000000 : ℝ)*x 1 + (674478973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037463/1953125 : ℝ)^259 ≤ (43158444446033/100000000000000 : ℝ)^195 := by
    have hnat : (1037463 : ℕ)^259*100000000000000^195 ≤ 43158444446033^195*1953125^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037463 1953125 43158444446033 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424803681/2000000000 : ℝ)^259 ≤ (510961481777/4000000000000 : ℝ)^195 := by
    have hnat : (424803681 : ℕ)^259*4000000000000^195 ≤ 510961481777^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424803681 2000000000 510961481777 4000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674478973/1250000000 : ℝ)^259 ≤ (22033759248913/50000000000000 : ℝ)^195 := by
    have hnat : (674478973 : ℕ)^259*50000000000000^195 ≤ 22033759248913^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674478973 1250000000 22033759248913 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037463/1953125 : ℝ), (-424803681/2000000000 : ℝ), (674478973/1250000000 : ℝ)] ![(43158444446033/100000000000000 : ℝ), (510961481777/4000000000000 : ℝ), (22033759248913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037463/1953125 : ℝ)|^259 ≤ (43158444446033/100000000000000 : ℝ)^195
        have hw : |(1037463/1953125 : ℝ)|=(1037463/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424803681/2000000000 : ℝ)|^259 ≤ (510961481777/4000000000000 : ℝ)^195
        have hw : |(-424803681/2000000000 : ℝ)|=(424803681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674478973/1250000000 : ℝ)|^259 ≤ (22033759248913/50000000000000 : ℝ)^195
        have hw : |(674478973/1250000000 : ℝ)|=(674478973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1327952639/2500000000 : ℝ)*x 0 + (5395831839/10000000000 : ℝ)*x 1 + (-66375573/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327952639/2500000000 : ℝ)^259 ≤ (43158444402867/100000000000000 : ℝ)^195 := by
    have hnat : (1327952639 : ℕ)^259*100000000000000^195 ≤ 43158444402867^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327952639 2500000000 43158444402867 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395831839/10000000000 : ℝ)^259 ≤ (44067519094433/100000000000000 : ℝ)^195 := by
    have hnat : (5395831839 : ℕ)^259*100000000000000^195 ≤ 44067519094433^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395831839 10000000000 44067519094433 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66375573/312500000 : ℝ)^259 ≤ (12774036493257/100000000000000 : ℝ)^195 := by
    have hnat : (66375573 : ℕ)^259*100000000000000^195 ≤ 12774036493257^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66375573 312500000 12774036493257 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327952639/2500000000 : ℝ), (5395831839/10000000000 : ℝ), (-66375573/312500000 : ℝ)] ![(43158444402867/100000000000000 : ℝ), (44067519094433/100000000000000 : ℝ), (12774036493257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327952639/2500000000 : ℝ)|^259 ≤ (43158444402867/100000000000000 : ℝ)^195
        have hw : |(1327952639/2500000000 : ℝ)|=(1327952639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395831839/10000000000 : ℝ)|^259 ≤ (44067519094433/100000000000000 : ℝ)^195
        have hw : |(5395831839/10000000000 : ℝ)|=(5395831839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66375573/312500000 : ℝ)|^259 ≤ (12774036493257/100000000000000 : ℝ)^195
        have hw : |(-66375573/312500000 : ℝ)|=(66375573/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s5_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (874246297/2000000000 : ℝ)*x 0 + (35187549/78125000 : ℝ)*x 1 + (1060604093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874246297/2000000000 : ℝ)^259 ≤ (33315637793963/100000000000000 : ℝ)^195 := by
    have hnat : (874246297 : ℕ)^259*100000000000000^195 ≤ 33315637793963^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874246297 2000000000 33315637793963 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35187549/78125000 : ℝ)^259 ≤ (8666593090731/25000000000000 : ℝ)^195 := by
    have hnat : (35187549 : ℕ)^259*25000000000000^195 ≤ 8666593090731^195*78125000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35187549 78125000 8666593090731 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060604093/2500000000 : ℝ)^259 ≤ (400224872791/1250000000000 : ℝ)^195 := by
    have hnat : (1060604093 : ℕ)^259*1250000000000^195 ≤ 400224872791^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060604093 2500000000 400224872791 1250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874246297/2000000000 : ℝ), (35187549/78125000 : ℝ), (1060604093/2500000000 : ℝ)] ![(33315637793963/100000000000000 : ℝ), (8666593090731/25000000000000 : ℝ), (400224872791/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874246297/2000000000 : ℝ)|^259 ≤ (33315637793963/100000000000000 : ℝ)^195
        have hw : |(874246297/2000000000 : ℝ)|=(874246297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35187549/78125000 : ℝ)|^259 ≤ (8666593090731/25000000000000 : ℝ)^195
        have hw : |(35187549/78125000 : ℝ)|=(35187549/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060604093/2500000000 : ℝ)|^259 ≤ (400224872791/1250000000000 : ℝ)^195
        have hw : |(1060604093/2500000000 : ℝ)|=(1060604093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11083/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (681214879766951/5000000000000000000 : ℝ) := by
    have hpowers : (11083/100000 : ℝ)^8287 ≤ (681214879766951/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11083 : ℕ)^8287*5000000000000000000^2048 ≤ 681214879766951^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11083 100000 681214879766951 5000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11083/100000 : ℝ)) (X := (681214879766951/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (9388380007560461/25000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8287 ≤ (9388380007560461/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8287*25000000000000000000^2048 ≤ 9388380007560461^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 9388380007560461 25000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (9388380007560461/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500681214879766951/2500000000000000000 : ℝ) ≤ (1250084167068571/1250000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (2500681214879766951/2500000000000000000 : ℝ)^2048 ≤ (1250084167068571/1250000000000000 : ℝ)^8287 := by
      have hnat : (2500681214879766951 : ℕ)^2048*1250000000000000^8287 ≤ 1250084167068571^8287*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500681214879766951 2500000000000000000 1250084167068571 1250000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084167068571/1250000000000000 : ℝ)) (X := (2500681214879766951/2500000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563299653400399701/1562500000000000000 : ℝ) ≤ (5000632267312959/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (1563299653400399701/1562500000000000000 : ℝ)^2048 ≤ (5000632267312959/5000000000000000 : ℝ)^8287 := by
      have hnat : (1563299653400399701 : ℕ)^2048*5000000000000000^8287 ≤ 5000632267312959^8287*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563299653400399701 1562500000000000000 5000632267312959 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000632267312959/5000000000000000 : ℝ)) (X := (1563299653400399701/1562500000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509388380007560461/12500000000000000000 : ℝ) ≤ (2500463933175817/2500000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (12509388380007560461/12500000000000000000 : ℝ)^2048 ≤ (2500463933175817/2500000000000000 : ℝ)^8287 := by
      have hnat : (12509388380007560461 : ℕ)^2048*2500000000000000^8287 ≤ 2500463933175817^8287*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509388380007560461 12500000000000000000 2500463933175817 2500000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500463933175817/2500000000000000 : ℝ)) (X := (12509388380007560461/12500000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(681214879766951/5000000000000000000 : ℝ) ≤ ((7887255138391185127/7890000000000000000 : ℝ)+2*(11823961547/6312000000000 : ℝ)*(11083/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (7887255138391185127/7890000000000000000 : ℝ)+2*(11823961547/6312000000000 : ℝ)*(11083/100000 : ℝ)=(1250084167068571/1250000000000000 : ℝ) by norm_num, show 1+2*(681214879766951/5000000000000000000 : ℝ)=(2500681214879766951/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9388380007560461/25000000000000000000 : ℝ)+(681214879766951/5000000000000000000 : ℝ) ≤ ((7887255138391185127/7890000000000000000 : ℝ)+(11823961547/6312000000000 : ℝ)*((14239/100000 : ℝ)+(11083/100000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (7887255138391185127/7890000000000000000 : ℝ)+(11823961547/6312000000000 : ℝ)*((14239/100000 : ℝ)+(11083/100000 : ℝ))=(5000632267312959/5000000000000000 : ℝ) by norm_num, show 1+(9388380007560461/25000000000000000000 : ℝ)+(681214879766951/5000000000000000000 : ℝ)=(1563299653400399701/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9388380007560461/25000000000000000000 : ℝ) ≤ ((7887255138391185127/7890000000000000000 : ℝ)+2*(11823961547/6312000000000 : ℝ)*(14239/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (7887255138391185127/7890000000000000000 : ℝ)+2*(11823961547/6312000000000 : ℝ)*(14239/100000 : ℝ)=(2500463933175817/2500000000000000 : ℝ) by norm_num, show 1+2*(9388380007560461/25000000000000000000 : ℝ)=(12509388380007560461/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7887255138391185127/7890000000000000000 : ℝ)*(X 1 0+X 2 0)+(11823961547/6312000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7887255138391185127/7890000000000000000 : ℝ)) (alpha := (11823961547/6312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7887255138391185127/7890000000000000000 : ℝ)*(X 0 1+X 2 1)+(11823961547/6312000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7887255138391185127/7890000000000000000 : ℝ)) (alpha := (11823961547/6312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7887255138391185127/7890000000000000000 : ℝ)*(X 0 2+X 1 2)+(11823961547/6312000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7887255138391185127/7890000000000000000 : ℝ)) (alpha := (11823961547/6312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189363209/10000000000 : ℝ)*X 0 0+(107923591/200000000 : ℝ)*X 0 1+(5262776073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345487849/10000000000 : ℝ)*X 1 0+(-564268383/2500000000 : ℝ)*X 1 1+(1315694237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069097621/2000000000 : ℝ)*X 2 0+(41115441/78125000 : ℝ)*X 2 1+(-2257073853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174848843/400000000 : ℝ)*X 0 0+(1060432803/2500000000 : ℝ)*X 0 1+(2252344191/5000000000 : ℝ)*X 0 2+(174848843/400000000 : ℝ)*X 1 0+(1060432803/2500000000 : ℝ)*X 1 1+(2252344191/5000000000 : ℝ)*X 1 2+(174848843/400000000 : ℝ)*X 2 0+(1060432803/2500000000 : ℝ)*X 2 1+(2252344191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109468423/500000000 : ℝ)*X 0 0+(1052624531/2000000000 : ℝ)*X 0 1+(1348957973/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1037463/1953125 : ℝ)*X 1 0+(-424803681/2000000000 : ℝ)*X 1 1+(674478973/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327952639/2500000000 : ℝ)*X 2 0+(5395831839/10000000000 : ℝ)*X 2 1+(-66375573/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874246297/2000000000 : ℝ)*X 0 0+(35187549/78125000 : ℝ)*X 0 1+(1060604093/2500000000 : ℝ)*X 0 2+(874246297/2000000000 : ℝ)*X 1 0+(35187549/78125000 : ℝ)*X 1 1+(1060604093/2500000000 : ℝ)*X 1 2+(874246297/2000000000 : ℝ)*X 2 0+(35187549/78125000 : ℝ)*X 2 1+(1060604093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (600240292015317076531691127/65750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (805678031/50000000000000 : ℝ)*(base19) + (1737049219/100000000000000 : ℝ)*(base23) + (124713507/100000000000000 : ℝ)*(lower2) + (19233641/3125000000000 : ℝ)*(upper3) + (16483713/100000000000000 : ℝ)*(upper5) + (5649577522503001/100000000000000 : ℝ)*(major0) + (5649577522503001/100000000000000 : ℝ)*(major1) + (5649577522503001/100000000000000 : ℝ)*(major2) + (1874034464054951/25000000000000 : ℝ)*(sp0) + (7496196653807019/100000000000000 : ℝ)*(sp1) + (3748098264056931/50000000000000 : ℝ)*(sp2) + (1901460565581737/50000000000000 : ℝ)*(sp3) + (60408943277/100000000000000 : ℝ)*(sp4) + (7068875021/20000000000000 : ℝ)*(sp7) + (1901478237769289/50000000000000 : ℝ)*(f.failure) + (7496198265163081/100000000000000 : ℝ)*(f.sum) + (9486449224753/1578000000000000000000000000 : ℝ)*base65 + (14215274063899183873/789000000000000000000000000000000 : ℝ)*base68 + (4976314421731816127/789000000000000000000000000000000 : ℝ)*base69 + (6254303453146183873/789000000000000000000000000000000 : ℝ)*base72 + (186467651317/315600000000000000000000000 : ℝ)*base74 + (11796451326472183873/789000000000000000000000000000000 : ℝ)*base76 + (4479999763177183873/789000000000000000000000000000000 : ℝ)*base78 + (6607320687748183873/789000000000000000000000000000000 : ℝ)*base80 + (733019978059/1578000000000000000000000000 : ℝ)*base81 + (5768879/625000000000000000000 : ℝ)*base90 + (5768879/625000000000000000000 : ℝ)*base92 + (5768879/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619401027767002598419090011/65750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610662933/50000000000000 : ℝ)*(base19) + (1574275693/100000000000000 : ℝ)*(base23) + (58949783/50000000000000 : ℝ)*(upper3) + (14987979/10000000000000 : ℝ)*(lower4) + (110174527/100000000000000 : ℝ)*(upper5) + (5679021770663307/100000000000000 : ℝ)*(major0) + (5679021770663307/100000000000000 : ℝ)*(major1) + (5679021770663307/100000000000000 : ℝ)*(major2) + (27284880283/100000000000000 : ℝ)*(sp1) + (7868901499/20000000000000 : ℝ)*(sp2) + (941908331410267/12500000000000 : ℝ)*(sp4) + (1883809536268997/25000000000000 : ℝ)*(sp5) + (1883806433124737/25000000000000 : ℝ)*(sp6) + (955694144006549/25000000000000 : ℝ)*(sp7) + (955694144006549/25000000000000 : ℝ)*(f.failure) + (941908331410267/12500000000000 : ℝ)*(f.sum) + (69030786043/105200000000000000000000000 : ℝ)*base65 + (4613593059748761663/263000000000000000000000000000000 : ℝ)*base67 + (2872435793932761663/263000000000000000000000000000000 : ℝ)*base69 + (390166885796238337/263000000000000000000000000000000 : ℝ)*base72 + (2756010697199/526000000000000000000000000 : ℝ)*base73 + (416268914600761663/263000000000000000000000000000000 : ℝ)*base75 + (505577577495761663/263000000000000000000000000000000 : ℝ)*base77 + (7580366650072761663/263000000000000000000000000000000 : ℝ)*base79 + (2022361922841/526000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5481739/312500000000000000000 : ℝ)*base90 + (5481739/312500000000000000000 : ℝ)*base92 + (5481739/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1095_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1095_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1095_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1095_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16647/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
