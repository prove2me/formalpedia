-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1001_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:50:12.690903+00:00
-- url     : https://prove2.me/submissions/d5fc3b2c-9d5d-41e7-b8a8-f58aa54c8a81

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
theorem support_rectangle_w1001_box_0 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104422569/10000000000 : ℝ)*x 0 + (1075645893/2000000000 : ℝ)*x 1 + (5378230021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104422569/10000000000 : ℝ)^4097 ≤ (6259707298357/50000000000000 : ℝ)^3073 := by
    have hnat : (2104422569 : ℕ)^4097*50000000000000^3073 ≤ 6259707298357^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104422569 10000000000 6259707298357 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075645893/2000000000 : ℝ)^4097 ≤ (21870144839099/50000000000000 : ℝ)^3073 := by
    have hnat : (1075645893 : ℕ)^4097*50000000000000^3073 ≤ 21870144839099^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075645893 2000000000 21870144839099 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378230021/10000000000 : ℝ)^4097 ≤ (8748059141371/20000000000000 : ℝ)^3073 := by
    have hnat : (5378230021 : ℕ)^4097*20000000000000^3073 ≤ 8748059141371^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378230021 10000000000 8748059141371 20000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104422569/10000000000 : ℝ), (1075645893/2000000000 : ℝ), (5378230021/10000000000 : ℝ)] ![(6259707298357/50000000000000 : ℝ), (21870144839099/50000000000000 : ℝ), (8748059141371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104422569/10000000000 : ℝ)|^4097 ≤ (6259707298357/50000000000000 : ℝ)^3073
        have hw : |(-2104422569/10000000000 : ℝ)|=(2104422569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075645893/2000000000 : ℝ)|^4097 ≤ (21870144839099/50000000000000 : ℝ)^3073
        have hw : |(1075645893/2000000000 : ℝ)|=(1075645893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378230021/10000000000 : ℝ)|^4097 ≤ (8748059141371/20000000000000 : ℝ)^3073
        have hw : |(5378230021/10000000000 : ℝ)|=(5378230021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_1 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647206061/5000000000 : ℝ)*x 0 + (-2217705259/10000000000 : ℝ)*x 1 + (1075645847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647206061/5000000000 : ℝ)^4097 ≤ (42833834089287/100000000000000 : ℝ)^3073 := by
    have hnat : (2647206061 : ℕ)^4097*100000000000000^3073 ≤ 42833834089287^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647206061 5000000000 42833834089287 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217705259/10000000000 : ℝ)^4097 ≤ (3356469676869/25000000000000 : ℝ)^3073 := by
    have hnat : (2217705259 : ℕ)^4097*25000000000000^3073 ≤ 3356469676869^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217705259 10000000000 3356469676869 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075645847/2000000000 : ℝ)^4097 ≤ (4374028718433/10000000000000 : ℝ)^3073 := by
    have hnat : (1075645847 : ℕ)^4097*10000000000000^3073 ≤ 4374028718433^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075645847 2000000000 4374028718433 10000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647206061/5000000000 : ℝ), (-2217705259/10000000000 : ℝ), (1075645847/2000000000 : ℝ)] ![(42833834089287/100000000000000 : ℝ), (3356469676869/25000000000000 : ℝ), (4374028718433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647206061/5000000000 : ℝ)|^4097 ≤ (42833834089287/100000000000000 : ℝ)^3073
        have hw : |(2647206061/5000000000 : ℝ)|=(2647206061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217705259/10000000000 : ℝ)|^4097 ≤ (3356469676869/25000000000000 : ℝ)^3073
        have hw : |(-2217705259/10000000000 : ℝ)|=(2217705259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075645847/2000000000 : ℝ)|^4097 ≤ (4374028718433/10000000000000 : ℝ)^3073
        have hw : |(1075645847/2000000000 : ℝ)|=(1075645847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_2 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294412129/10000000000 : ℝ)*x 0 + (2689114663/5000000000 : ℝ)*x 1 + (-2217705129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294412129/10000000000 : ℝ)^4097 ≤ (42833834164791/100000000000000 : ℝ)^3073 := by
    have hnat : (5294412129 : ℕ)^4097*100000000000000^3073 ≤ 42833834164791^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294412129 10000000000 42833834164791 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689114663/5000000000 : ℝ)^4097 ≤ (21870144085517/50000000000000 : ℝ)^3073 := by
    have hnat : (2689114663 : ℕ)^4097*50000000000000^3073 ≤ 21870144085517^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689114663 5000000000 21870144085517 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217705129/10000000000 : ℝ)^4097 ≤ (1342587765821/10000000000000 : ℝ)^3073 := by
    have hnat : (2217705129 : ℕ)^4097*10000000000000^3073 ≤ 1342587765821^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217705129 10000000000 1342587765821 10000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294412129/10000000000 : ℝ), (2689114663/5000000000 : ℝ), (-2217705129/10000000000 : ℝ)] ![(42833834164791/100000000000000 : ℝ), (21870144085517/50000000000000 : ℝ), (1342587765821/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294412129/10000000000 : ℝ)|^4097 ≤ (42833834164791/100000000000000 : ℝ)^3073
        have hw : |(5294412129/10000000000 : ℝ)|=(5294412129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689114663/5000000000 : ℝ)|^4097 ≤ (21870144085517/50000000000000 : ℝ)^3073
        have hw : |(2689114663/5000000000 : ℝ)|=(2689114663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217705129/10000000000 : ℝ)|^4097 ≤ (1342587765821/10000000000000 : ℝ)^3073
        have hw : |(-2217705129/10000000000 : ℝ)|=(2217705129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_3 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (561760441/1250000000 : ℝ)*x 0 + (2166278797/5000000000 : ℝ)*x 1 + (4332557871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (561760441/1250000000 : ℝ)^4097 ≤ (8606618261221/25000000000000 : ℝ)^3073 := by
    have hnat : (561760441 : ℕ)^4097*25000000000000^3073 ≤ 8606618261221^3073*1250000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561760441 1250000000 8606618261221 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166278797/5000000000 : ℝ)^4097 ≤ (512293157399/1562500000000 : ℝ)^3073 := by
    have hnat : (2166278797 : ℕ)^4097*1562500000000^3073 ≤ 512293157399^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166278797 5000000000 512293157399 1562500000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4332557871/10000000000 : ℝ)^4097 ≤ (131147059473/400000000000 : ℝ)^3073 := by
    have hnat : (4332557871 : ℕ)^4097*400000000000^3073 ≤ 131147059473^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332557871 10000000000 131147059473 400000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(561760441/1250000000 : ℝ), (2166278797/5000000000 : ℝ), (4332557871/10000000000 : ℝ)] ![(8606618261221/25000000000000 : ℝ), (512293157399/1562500000000 : ℝ), (131147059473/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(561760441/1250000000 : ℝ)|^4097 ≤ (8606618261221/25000000000000 : ℝ)^3073
        have hw : |(561760441/1250000000 : ℝ)|=(561760441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166278797/5000000000 : ℝ)|^4097 ≤ (512293157399/1562500000000 : ℝ)^3073
        have hw : |(2166278797/5000000000 : ℝ)|=(2166278797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4332557871/10000000000 : ℝ)|^4097 ≤ (131147059473/400000000000 : ℝ)^3073
        have hw : |(4332557871/10000000000 : ℝ)|=(4332557871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_4 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-592332287/2500000000 : ℝ)*x 0 + (1319764287/2500000000 : ℝ)*x 1 + (5279057763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592332287/2500000000 : ℝ)^4097 ≤ (14663411816299/100000000000000 : ℝ)^3073 := by
    have hnat : (592332287 : ℕ)^4097*100000000000000^3073 ≤ 14663411816299^3073*2500000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592332287 2500000000 14663411816299 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319764287/2500000000 : ℝ)^4097 ≤ (42668290772613/100000000000000 : ℝ)^3073 := by
    have hnat : (1319764287 : ℕ)^4097*100000000000000^3073 ≤ 42668290772613^3073*2500000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319764287 2500000000 42668290772613 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279057763/10000000000 : ℝ)^4097 ≤ (42668297399773/100000000000000 : ℝ)^3073 := by
    have hnat : (5279057763 : ℕ)^4097*100000000000000^3073 ≤ 42668297399773^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279057763 10000000000 42668297399773 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-592332287/2500000000 : ℝ), (1319764287/2500000000 : ℝ), (5279057763/10000000000 : ℝ)] ![(14663411816299/100000000000000 : ℝ), (42668290772613/100000000000000 : ℝ), (42668297399773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-592332287/2500000000 : ℝ)|^4097 ≤ (14663411816299/100000000000000 : ℝ)^3073
        have hw : |(-592332287/2500000000 : ℝ)|=(592332287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319764287/2500000000 : ℝ)|^4097 ≤ (42668290772613/100000000000000 : ℝ)^3073
        have hw : |(1319764287/2500000000 : ℝ)|=(1319764287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279057763/10000000000 : ℝ)|^4097 ≤ (42668297399773/100000000000000 : ℝ)^3073
        have hw : |(5279057763/10000000000 : ℝ)|=(5279057763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_5 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134117577/250000000 : ℝ)*x 0 + (-451253353/2000000000 : ℝ)*x 1 + (659882211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134117577/250000000 : ℝ)^4097 ≤ (43593685836473/100000000000000 : ℝ)^3073 := by
    have hnat : (134117577 : ℕ)^4097*100000000000000^3073 ≤ 43593685836473^3073*250000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134117577 250000000 43593685836473 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451253353/2000000000 : ℝ)^4097 ≤ (343450438977/2500000000000 : ℝ)^3073 := by
    have hnat : (451253353 : ℕ)^4097*2500000000000^3073 ≤ 343450438977^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451253353 2000000000 343450438977 2500000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659882211/1250000000 : ℝ)^4097 ≤ (21334148295791/50000000000000 : ℝ)^3073 := by
    have hnat : (659882211 : ℕ)^4097*50000000000000^3073 ≤ 21334148295791^3073*1250000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659882211 1250000000 21334148295791 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134117577/250000000 : ℝ), (-451253353/2000000000 : ℝ), (659882211/1250000000 : ℝ)] ![(43593685836473/100000000000000 : ℝ), (343450438977/2500000000000 : ℝ), (21334148295791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134117577/250000000 : ℝ)|^4097 ≤ (43593685836473/100000000000000 : ℝ)^3073
        have hw : |(134117577/250000000 : ℝ)|=(134117577/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451253353/2000000000 : ℝ)|^4097 ≤ (343450438977/2500000000000 : ℝ)^3073
        have hw : |(-451253353/2000000000 : ℝ)|=(451253353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659882211/1250000000 : ℝ)|^4097 ≤ (21334148295791/50000000000000 : ℝ)^3073
        have hw : |(659882211/1250000000 : ℝ)|=(659882211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_6 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335293999/625000000 : ℝ)*x 0 + (527905703/1000000000 : ℝ)*x 1 + (-35254163/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335293999/625000000 : ℝ)^4097 ≤ (272460597689/625000000000 : ℝ)^3073 := by
    have hnat : (335293999 : ℕ)^4097*625000000000^3073 ≤ 272460597689^3073*625000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335293999 625000000 272460597689 625000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527905703/1000000000 : ℝ)^4097 ≤ (42668289501061/100000000000000 : ℝ)^3073 := by
    have hnat : (527905703 : ℕ)^4097*100000000000000^3073 ≤ 42668289501061^3073*1000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527905703 1000000000 42668289501061 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35254163/156250000 : ℝ)^4097 ≤ (13738014855861/100000000000000 : ℝ)^3073 := by
    have hnat : (35254163 : ℕ)^4097*100000000000000^3073 ≤ 13738014855861^3073*156250000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35254163 156250000 13738014855861 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335293999/625000000 : ℝ), (527905703/1000000000 : ℝ), (-35254163/156250000 : ℝ)] ![(272460597689/625000000000 : ℝ), (42668289501061/100000000000000 : ℝ), (13738014855861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335293999/625000000 : ℝ)|^4097 ≤ (272460597689/625000000000 : ℝ)^3073
        have hw : |(335293999/625000000 : ℝ)|=(335293999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527905703/1000000000 : ℝ)|^4097 ≤ (42668289501061/100000000000000 : ℝ)^3073
        have hw : |(527905703/1000000000 : ℝ)|=(527905703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35254163/156250000 : ℝ)|^4097 ≤ (13738014855861/100000000000000 : ℝ)^3073
        have hw : |(-35254163/156250000 : ℝ)|=(35254163/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_7 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275467077/10000000000 : ℝ)*x 0 + (2220922263/5000000000 : ℝ)*x 1 + (1110460833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275467077/10000000000 : ℝ)^4097 ≤ (32212031603607/100000000000000 : ℝ)^3073 := by
    have hnat : (4275467077 : ℕ)^4097*100000000000000^3073 ≤ 32212031603607^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275467077 10000000000 32212031603607 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220922263/5000000000 : ℝ)^4097 ≤ (33893990264597/100000000000000 : ℝ)^3073 := by
    have hnat : (2220922263 : ℕ)^4097*100000000000000^3073 ≤ 33893990264597^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220922263 5000000000 33893990264597 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110460833/2500000000 : ℝ)^4097 ≤ (8473494529413/25000000000000 : ℝ)^3073 := by
    have hnat : (1110460833 : ℕ)^4097*25000000000000^3073 ≤ 8473494529413^3073*2500000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110460833 2500000000 8473494529413 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275467077/10000000000 : ℝ), (2220922263/5000000000 : ℝ), (1110460833/2500000000 : ℝ)] ![(32212031603607/100000000000000 : ℝ), (33893990264597/100000000000000 : ℝ), (8473494529413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275467077/10000000000 : ℝ)|^4097 ≤ (32212031603607/100000000000000 : ℝ)^3073
        have hw : |(4275467077/10000000000 : ℝ)|=(4275467077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220922263/5000000000 : ℝ)|^4097 ≤ (33893990264597/100000000000000 : ℝ)^3073
        have hw : |(2220922263/5000000000 : ℝ)|=(2220922263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1110460833/2500000000 : ℝ)|^4097 ≤ (8473494529413/25000000000000 : ℝ)^3073
        have hw : |(1110460833/2500000000 : ℝ)|=(1110460833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_8 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2314113229/10000000000 : ℝ)*x 0 + (1042378929/2000000000 : ℝ)*x 1 + (5387819859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2314113229/10000000000 : ℝ)^4097 ≤ (14209596736943/100000000000000 : ℝ)^3073 := by
    have hnat : (2314113229 : ℕ)^4097*100000000000000^3073 ≤ 14209596736943^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314113229 10000000000 14209596736943 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042378929/2000000000 : ℝ)^4097 ≤ (8389218987953/20000000000000 : ℝ)^3073 := by
    have hnat : (1042378929 : ℕ)^4097*20000000000000^3073 ≤ 8389218987953^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042378929 2000000000 8389218987953 20000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387819859/10000000000 : ℝ)^4097 ≤ (21922154155317/50000000000000 : ℝ)^3073 := by
    have hnat : (5387819859 : ℕ)^4097*50000000000000^3073 ≤ 21922154155317^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387819859 10000000000 21922154155317 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2314113229/10000000000 : ℝ), (1042378929/2000000000 : ℝ), (5387819859/10000000000 : ℝ)] ![(14209596736943/100000000000000 : ℝ), (8389218987953/20000000000000 : ℝ), (21922154155317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2314113229/10000000000 : ℝ)|^4097 ≤ (14209596736943/100000000000000 : ℝ)^3073
        have hw : |(-2314113229/10000000000 : ℝ)|=(2314113229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042378929/2000000000 : ℝ)|^4097 ≤ (8389218987953/20000000000000 : ℝ)^3073
        have hw : |(1042378929/2000000000 : ℝ)|=(1042378929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387819859/10000000000 : ℝ)|^4097 ≤ (21922154155317/50000000000000 : ℝ)^3073
        have hw : |(5387819859/10000000000 : ℝ)|=(5387819859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_9 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287609929/10000000000 : ℝ)*x 0 + (-2213903981/10000000000 : ℝ)*x 1 + (269391021/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287609929/10000000000 : ℝ)^4097 ≤ (342083834287/800000000000 : ℝ)^3073 := by
    have hnat : (5287609929 : ℕ)^4097*800000000000^3073 ≤ 342083834287^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287609929 10000000000 342083834287 800000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213903981/10000000000 : ℝ)^4097 ≤ (669760315101/5000000000000 : ℝ)^3073 := by
    have hnat : (2213903981 : ℕ)^4097*5000000000000^3073 ≤ 669760315101^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213903981 10000000000 669760315101 5000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269391021/500000000 : ℝ)^4097 ≤ (43844314397117/100000000000000 : ℝ)^3073 := by
    have hnat : (269391021 : ℕ)^4097*100000000000000^3073 ≤ 43844314397117^3073*500000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269391021 500000000 43844314397117 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287609929/10000000000 : ℝ), (-2213903981/10000000000 : ℝ), (269391021/500000000 : ℝ)] ![(342083834287/800000000000 : ℝ), (669760315101/5000000000000 : ℝ), (43844314397117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287609929/10000000000 : ℝ)|^4097 ≤ (342083834287/800000000000 : ℝ)^3073
        have hw : |(5287609929/10000000000 : ℝ)|=(5287609929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213903981/10000000000 : ℝ)|^4097 ≤ (669760315101/5000000000000 : ℝ)^3073
        have hw : |(-2213903981/10000000000 : ℝ)|=(2213903981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269391021/500000000 : ℝ)|^4097 ≤ (43844314397117/100000000000000 : ℝ)^3073
        have hw : |(269391021/500000000 : ℝ)|=(269391021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_10 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287610773/10000000000 : ℝ)*x 0 + (538781989/1000000000 : ℝ)*x 1 + (-442780713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287610773/10000000000 : ℝ)^4097 ≤ (2672530524101/6250000000000 : ℝ)^3073 := by
    have hnat : (5287610773 : ℕ)^4097*6250000000000^3073 ≤ 2672530524101^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287610773 10000000000 2672530524101 6250000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538781989/1000000000 : ℝ)^4097 ≤ (10961077161741/25000000000000 : ℝ)^3073 := by
    have hnat : (538781989 : ℕ)^4097*25000000000000^3073 ≤ 10961077161741^3073*1000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538781989 1000000000 10961077161741 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442780713/2000000000 : ℝ)^4097 ≤ (837200184143/6250000000000 : ℝ)^3073 := by
    have hnat : (442780713 : ℕ)^4097*6250000000000^3073 ≤ 837200184143^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442780713 2000000000 837200184143 6250000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287610773/10000000000 : ℝ), (538781989/1000000000 : ℝ), (-442780713/2000000000 : ℝ)] ![(2672530524101/6250000000000 : ℝ), (10961077161741/25000000000000 : ℝ), (837200184143/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287610773/10000000000 : ℝ)|^4097 ≤ (2672530524101/6250000000000 : ℝ)^3073
        have hw : |(5287610773/10000000000 : ℝ)|=(5287610773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538781989/1000000000 : ℝ)|^4097 ≤ (10961077161741/25000000000000 : ℝ)^3073
        have hw : |(538781989/1000000000 : ℝ)|=(538781989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442780713/2000000000 : ℝ)|^4097 ≤ (837200184143/6250000000000 : ℝ)^3073
        have hw : |(-442780713/2000000000 : ℝ)|=(442780713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_11 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564368873/1250000000 : ℝ)*x 0 + (4321983697/10000000000 : ℝ)*x 1 + (2160991649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564368873/1250000000 : ℝ)^4097 ≤ (8659939449617/25000000000000 : ℝ)^3073 := by
    have hnat : (564368873 : ℕ)^4097*25000000000000^3073 ≤ 8659939449617^3073*1250000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564368873 1250000000 8659939449617 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321983697/10000000000 : ℝ)^4097 ≤ (4085015388137/12500000000000 : ℝ)^3073 := by
    have hnat : (4321983697 : ℕ)^4097*12500000000000^3073 ≤ 4085015388137^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321983697 10000000000 4085015388137 12500000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160991649/5000000000 : ℝ)^4097 ≤ (16340059541387/50000000000000 : ℝ)^3073 := by
    have hnat : (2160991649 : ℕ)^4097*50000000000000^3073 ≤ 16340059541387^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160991649 5000000000 16340059541387 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564368873/1250000000 : ℝ), (4321983697/10000000000 : ℝ), (2160991649/5000000000 : ℝ)] ![(8659939449617/25000000000000 : ℝ), (4085015388137/12500000000000 : ℝ), (16340059541387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564368873/1250000000 : ℝ)|^4097 ≤ (8659939449617/25000000000000 : ℝ)^3073
        have hw : |(564368873/1250000000 : ℝ)|=(564368873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321983697/10000000000 : ℝ)|^4097 ≤ (4085015388137/12500000000000 : ℝ)^3073
        have hw : |(4321983697/10000000000 : ℝ)|=(4321983697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160991649/5000000000 : ℝ)|^4097 ≤ (16340059541387/50000000000000 : ℝ)^3073
        have hw : |(2160991649/5000000000 : ℝ)|=(2160991649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_12 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432010373/2000000000 : ℝ)*x 0 + (5444004313/10000000000 : ℝ)*x 1 + (5271093857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432010373/2000000000 : ℝ)^4097 ≤ (12962569480263/100000000000000 : ℝ)^3073 := by
    have hnat : (432010373 : ℕ)^4097*100000000000000^3073 ≤ 12962569480263^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432010373 2000000000 12962569480263 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444004313/10000000000 : ℝ)^4097 ≤ (22227464765949/50000000000000 : ℝ)^3073 := by
    have hnat : (5444004313 : ℕ)^4097*50000000000000^3073 ≤ 22227464765949^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444004313 10000000000 22227464765949 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271093857/10000000000 : ℝ)^4097 ≤ (4258250096949/10000000000000 : ℝ)^3073 := by
    have hnat : (5271093857 : ℕ)^4097*10000000000000^3073 ≤ 4258250096949^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271093857 10000000000 4258250096949 10000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432010373/2000000000 : ℝ), (5444004313/10000000000 : ℝ), (5271093857/10000000000 : ℝ)] ![(12962569480263/100000000000000 : ℝ), (22227464765949/50000000000000 : ℝ), (4258250096949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432010373/2000000000 : ℝ)|^4097 ≤ (12962569480263/100000000000000 : ℝ)^3073
        have hw : |(-432010373/2000000000 : ℝ)|=(432010373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444004313/10000000000 : ℝ)|^4097 ≤ (22227464765949/50000000000000 : ℝ)^3073
        have hw : |(5444004313/10000000000 : ℝ)|=(5444004313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271093857/10000000000 : ℝ)|^4097 ≤ (4258250096949/10000000000000 : ℝ)^3073
        have hw : |(5271093857/10000000000 : ℝ)|=(5271093857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_13 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685172711/5000000000 : ℝ)*x 0 + (-1129651851/5000000000 : ℝ)*x 1 + (1317773421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685172711/5000000000 : ℝ)^4097 ≤ (43654824619449/100000000000000 : ℝ)^3073 := by
    have hnat : (2685172711 : ℕ)^4097*100000000000000^3073 ≤ 43654824619449^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685172711 5000000000 43654824619449 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129651851/5000000000 : ℝ)^4097 ≤ (3440669064563/25000000000000 : ℝ)^3073 := by
    have hnat : (1129651851 : ℕ)^4097*25000000000000^3073 ≤ 3440669064563^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129651851 5000000000 3440669064563 25000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317773421/2500000000 : ℝ)^4097 ≤ (21291249553101/50000000000000 : ℝ)^3073 := by
    have hnat : (1317773421 : ℕ)^4097*50000000000000^3073 ≤ 21291249553101^3073*2500000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317773421 2500000000 21291249553101 50000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685172711/5000000000 : ℝ), (-1129651851/5000000000 : ℝ), (1317773421/2500000000 : ℝ)] ![(43654824619449/100000000000000 : ℝ), (3440669064563/25000000000000 : ℝ), (21291249553101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685172711/5000000000 : ℝ)|^4097 ≤ (43654824619449/100000000000000 : ℝ)^3073
        have hw : |(2685172711/5000000000 : ℝ)|=(2685172711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129651851/5000000000 : ℝ)|^4097 ≤ (3440669064563/25000000000000 : ℝ)^3073
        have hw : |(-1129651851/5000000000 : ℝ)|=(1129651851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317773421/2500000000 : ℝ)|^4097 ≤ (21291249553101/50000000000000 : ℝ)^3073
        have hw : |(1317773421/2500000000 : ℝ)|=(1317773421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_14 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370345283/10000000000 : ℝ)*x 0 + (2635547003/5000000000 : ℝ)*x 1 + (-2259303461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370345283/10000000000 : ℝ)^4097 ≤ (43654823113021/100000000000000 : ℝ)^3073 := by
    have hnat : (5370345283 : ℕ)^4097*100000000000000^3073 ≤ 43654823113021^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370345283 10000000000 43654823113021 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635547003/5000000000 : ℝ)^4097 ≤ (42582502574287/100000000000000 : ℝ)^3073 := by
    have hnat : (2635547003 : ℕ)^4097*100000000000000^3073 ≤ 42582502574287^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635547003 5000000000 42582502574287 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259303461/10000000000 : ℝ)^4097 ≤ (13762674300991/100000000000000 : ℝ)^3073 := by
    have hnat : (2259303461 : ℕ)^4097*100000000000000^3073 ≤ 13762674300991^3073*10000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259303461 10000000000 13762674300991 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370345283/10000000000 : ℝ), (2635547003/5000000000 : ℝ), (-2259303461/10000000000 : ℝ)] ![(43654823113021/100000000000000 : ℝ), (42582502574287/100000000000000 : ℝ), (13762674300991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370345283/10000000000 : ℝ)|^4097 ≤ (43654823113021/100000000000000 : ℝ)^3073
        have hw : |(5370345283/10000000000 : ℝ)|=(5370345283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635547003/5000000000 : ℝ)|^4097 ≤ (42582502574287/100000000000000 : ℝ)^3073
        have hw : |(2635547003/5000000000 : ℝ)|=(2635547003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2259303461/10000000000 : ℝ)|^4097 ≤ (13762674300991/100000000000000 : ℝ)^3073
        have hw : |(-2259303461/10000000000 : ℝ)|=(2259303461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1001_box_15 (p : ℝ) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851536351/2000000000 : ℝ)*x 0 + (139081733/312500000 : ℝ)*x 1 + (2225307477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851536351/2000000000 : ℝ)^4097 ≤ (1601675345417/5000000000000 : ℝ)^3073 := by
    have hnat : (851536351 : ℕ)^4097*5000000000000^3073 ≤ 1601675345417^3073*2000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851536351 2000000000 1601675345417 5000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139081733/312500000 : ℝ)^4097 ≤ (33983249094733/100000000000000 : ℝ)^3073 := by
    have hnat : (139081733 : ℕ)^4097*100000000000000^3073 ≤ 33983249094733^3073*312500000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139081733 312500000 33983249094733 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225307477/5000000000 : ℝ)^4097 ≤ (33983243984367/100000000000000 : ℝ)^3073 := by
    have hnat : (2225307477 : ℕ)^4097*100000000000000^3073 ≤ 33983243984367^3073*5000000000^4097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225307477 5000000000 33983243984367 100000000000000 4097 3073 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4097/1024 : ℝ)) 4097 3073 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851536351/2000000000 : ℝ), (139081733/312500000 : ℝ), (2225307477/5000000000 : ℝ)] ![(1601675345417/5000000000000 : ℝ), (33983249094733/100000000000000 : ℝ), (33983243984367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851536351/2000000000 : ℝ)|^4097 ≤ (1601675345417/5000000000000 : ℝ)^3073
        have hw : |(851536351/2000000000 : ℝ)|=(851536351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139081733/312500000 : ℝ)|^4097 ≤ (33983249094733/100000000000000 : ℝ)^3073
        have hw : |(139081733/312500000 : ℝ)|=(139081733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2225307477/5000000000 : ℝ)|^4097 ≤ (33983243984367/100000000000000 : ℝ)^3073
        have hw : |(2225307477/5000000000 : ℝ)|=(2225307477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1001_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4585319/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59193/100000 : ℝ) ∧ (15873/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82803/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (8193/2048 : ℝ) ≤ (3099001356595031/20000000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^8193 ≤ (3099001356595031/20000000000000000000 : ℝ)^2048 := by
      have hnat : (279 : ℕ)^8193*20000000000000000000^2048 ≤ 3099001356595031^2048*2500^8193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 3099001356595031 20000000000000000000 8193 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (3099001356595031/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8193 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13961/100000 : ℝ) ^ (8193/2048 : ℝ) ≤ (474415205482553/1250000000000000000 : ℝ) := by
    have hpowers : (13961/100000 : ℝ)^8193 ≤ (474415205482553/1250000000000000000 : ℝ)^2048 := by
      have hnat : (13961 : ℕ)^8193*1250000000000000000^2048 ≤ 474415205482553^2048*100000^8193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13961 100000 474415205482553 1250000000000000000 8193 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13961/100000 : ℝ)) (X := (474415205482553/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8193 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003099001356595031/10000000000000000000 : ℝ) ≤ (5000387282882281/5000000000000000 : ℝ) ^ (8193/2048 : ℝ) := by
    have hpowers : (10003099001356595031/10000000000000000000 : ℝ)^2048 ≤ (5000387282882281/5000000000000000 : ℝ)^8193 := by
      have hnat : (10003099001356595031 : ℕ)^2048*5000000000000000^8193 ≤ 5000387282882281^8193*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003099001356595031 10000000000000000000 5000387282882281 5000000000000000 2048 8193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000387282882281/5000000000000000 : ℝ)) (X := (10003099001356595031/10000000000000000000 : ℝ)) (by norm_num) 8193 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010689644644315879/20000000000000000000 : ℝ) ≤ (10001335774777871/10000000000000000 : ℝ) ^ (8193/2048 : ℝ) := by
    have hpowers : (20010689644644315879/20000000000000000000 : ℝ)^2048 ≤ (10001335774777871/10000000000000000 : ℝ)^8193 := by
      have hnat : (20010689644644315879 : ℕ)^2048*10000000000000000^8193 ≤ 10001335774777871^8193*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010689644644315879 20000000000000000000 10001335774777871 10000000000000000 2048 8193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001335774777871/10000000000000000 : ℝ)) (X := (20010689644644315879/20000000000000000000 : ℝ)) (by norm_num) 8193 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (625474415205482553/625000000000000000 : ℝ) ≤ (500094849189559/500000000000000 : ℝ) ^ (8193/2048 : ℝ) := by
    have hpowers : (625474415205482553/625000000000000000 : ℝ)^2048 ≤ (500094849189559/500000000000000 : ℝ)^8193 := by
      have hnat : (625474415205482553 : ℕ)^2048*500000000000000^8193 ≤ 500094849189559^8193*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625474415205482553 625000000000000000 500094849189559 500000000000000 2048 8193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500094849189559/500000000000000 : ℝ)) (X := (625474415205482553/625000000000000000 : ℝ)) (by norm_num) 8193 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3099001356595031/20000000000000000000 : ℝ) ≤ ((13999821686764740641/14005000000000000000 : ℝ)+2*(561209013309/280100000000000 : ℝ)*(279/2500 : ℝ))^(8193/2048 : ℝ) := by
    rw [show (13999821686764740641/14005000000000000000 : ℝ)+2*(561209013309/280100000000000 : ℝ)*(279/2500 : ℝ)=(5000387282882281/5000000000000000 : ℝ) by norm_num, show 1+2*(3099001356595031/20000000000000000000 : ℝ)=(10003099001356595031/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(474415205482553/1250000000000000000 : ℝ)+(3099001356595031/20000000000000000000 : ℝ) ≤ ((13999821686764740641/14005000000000000000 : ℝ)+(561209013309/280100000000000 : ℝ)*((13961/100000 : ℝ)+(279/2500 : ℝ)))^(8193/2048 : ℝ) := by
    rw [show (13999821686764740641/14005000000000000000 : ℝ)+(561209013309/280100000000000 : ℝ)*((13961/100000 : ℝ)+(279/2500 : ℝ))=(10001335774777871/10000000000000000 : ℝ) by norm_num, show 1+(474415205482553/1250000000000000000 : ℝ)+(3099001356595031/20000000000000000000 : ℝ)=(20010689644644315879/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(474415205482553/1250000000000000000 : ℝ) ≤ ((13999821686764740641/14005000000000000000 : ℝ)+2*(561209013309/280100000000000 : ℝ)*(13961/100000 : ℝ))^(8193/2048 : ℝ) := by
    rw [show (13999821686764740641/14005000000000000000 : ℝ)+2*(561209013309/280100000000000 : ℝ)*(13961/100000 : ℝ)=(500094849189559/500000000000000 : ℝ) by norm_num, show 1+2*(474415205482553/1250000000000000000 : ℝ)=(625474415205482553/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13999821686764740641/14005000000000000000 : ℝ)*(X 1 0+X 2 0)+(561209013309/280100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8193/2048 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (13961/100000 : ℝ)) (c := (13999821686764740641/14005000000000000000 : ℝ)) (alpha := (561209013309/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13999821686764740641/14005000000000000000 : ℝ)*(X 0 1+X 2 1)+(561209013309/280100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8193/2048 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (13961/100000 : ℝ)) (c := (13999821686764740641/14005000000000000000 : ℝ)) (alpha := (561209013309/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13999821686764740641/14005000000000000000 : ℝ)*(X 0 2+X 1 2)+(561209013309/280100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8193/2048 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (13961/100000 : ℝ)) (c := (13999821686764740641/14005000000000000000 : ℝ)) (alpha := (561209013309/280100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2104422569/10000000000 : ℝ)*X 0 0+(1075645893/2000000000 : ℝ)*X 0 1+(5378230021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647206061/5000000000 : ℝ)*X 1 0+(-2217705259/10000000000 : ℝ)*X 1 1+(1075645847/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294412129/10000000000 : ℝ)*X 2 0+(2689114663/5000000000 : ℝ)*X 2 1+(-2217705129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((561760441/1250000000 : ℝ)*X 0 0+(2166278797/5000000000 : ℝ)*X 0 1+(4332557871/10000000000 : ℝ)*X 0 2+(561760441/1250000000 : ℝ)*X 1 0+(2166278797/5000000000 : ℝ)*X 1 1+(4332557871/10000000000 : ℝ)*X 1 2+(561760441/1250000000 : ℝ)*X 2 0+(2166278797/5000000000 : ℝ)*X 2 1+(4332557871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-592332287/2500000000 : ℝ)*X 0 0+(1319764287/2500000000 : ℝ)*X 0 1+(5279057763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((134117577/250000000 : ℝ)*X 1 0+(-451253353/2000000000 : ℝ)*X 1 1+(659882211/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335293999/625000000 : ℝ)*X 2 0+(527905703/1000000000 : ℝ)*X 2 1+(-35254163/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275467077/10000000000 : ℝ)*X 0 0+(2220922263/5000000000 : ℝ)*X 0 1+(1110460833/2500000000 : ℝ)*X 0 2+(4275467077/10000000000 : ℝ)*X 1 0+(2220922263/5000000000 : ℝ)*X 1 1+(1110460833/2500000000 : ℝ)*X 1 2+(4275467077/10000000000 : ℝ)*X 2 0+(2220922263/5000000000 : ℝ)*X 2 1+(1110460833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2314113229/10000000000 : ℝ)*X 0 0+(1042378929/2000000000 : ℝ)*X 0 1+(5387819859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287609929/10000000000 : ℝ)*X 1 0+(-2213903981/10000000000 : ℝ)*X 1 1+(269391021/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287610773/10000000000 : ℝ)*X 2 0+(538781989/1000000000 : ℝ)*X 2 1+(-442780713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564368873/1250000000 : ℝ)*X 0 0+(4321983697/10000000000 : ℝ)*X 0 1+(2160991649/5000000000 : ℝ)*X 0 2+(564368873/1250000000 : ℝ)*X 1 0+(4321983697/10000000000 : ℝ)*X 1 1+(2160991649/5000000000 : ℝ)*X 1 2+(564368873/1250000000 : ℝ)*X 2 0+(4321983697/10000000000 : ℝ)*X 2 1+(2160991649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-432010373/2000000000 : ℝ)*X 0 0+(5444004313/10000000000 : ℝ)*X 0 1+(5271093857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2685172711/5000000000 : ℝ)*X 1 0+(-1129651851/5000000000 : ℝ)*X 1 1+(1317773421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370345283/10000000000 : ℝ)*X 2 0+(2635547003/5000000000 : ℝ)*X 2 1+(-2259303461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((851536351/2000000000 : ℝ)*X 0 0+(139081733/312500000 : ℝ)*X 0 1+(2225307477/5000000000 : ℝ)*X 0 2+(851536351/2000000000 : ℝ)*X 1 0+(139081733/312500000 : ℝ)*X 1 1+(2225307477/5000000000 : ℝ)*X 1 2+(851536351/2000000000 : ℝ)*X 2 0+(139081733/312500000 : ℝ)*X 2 1+(2225307477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1001_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-8713957260150222896977491721509/14005000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110035389/100000000000000 : ℝ)*(upper1) + (104222987/50000000000000 : ℝ)*(lower2) + (188151637/100000000000000 : ℝ)*(upper4) + (76023354596539/2000000000000 : ℝ)*(major0) + (76023354596539/2000000000000 : ℝ)*(major1) + (76023354596539/2000000000000 : ℝ)*(major2) + (163529581/4000000000000 : ℝ)*(sp2) + (239773011/100000000000000 : ℝ)*(sp3) + (629061228638011/12500000000000 : ℝ)*(sp4) + (5032440168826547/100000000000000 : ℝ)*(sp5) + (2516244272956209/50000000000000 : ℝ)*(sp6) + (1295291347916413/50000000000000 : ℝ)*(sp7) + (561009571/20000000000000 : ℝ)*(sp8) + (13116331349/25000000000000 : ℝ)*(sp13) + (647645733901459/25000000000000 : ℝ)*(f.failure) + (5032492634151943/100000000000000 : ℝ)*(f.sum) + (355563919119/2801000000000000000000000000 : ℝ)*base65 + (70404311478298501/28010000000000000000000000000000 : ℝ)*base68 + (329865420081228501/28010000000000000000000000000000 : ℝ)*base70 + (900970017830028501/28010000000000000000000000000000 : ℝ)*base72 + (4588979680453/2801000000000000000000000000 : ℝ)*base74 + (246772483735338501/28010000000000000000000000000000 : ℝ)*base76 + (406629095151678501/28010000000000000000000000000000 : ℝ)*base78 + (194736533338208501/28010000000000000000000000000000 : ℝ)*base80 + (3675029441199/1400500000000000000000000000 : ℝ)*base81 + (607079/78125000000000000000 : ℝ)*base90 + (607079/78125000000000000000 : ℝ)*base92 + (607079/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59193/100000 : ℝ) ≤ (4145167449331555753511054967/7002500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5251879/6250000000000 : ℝ)*(upper0) + (11918929/25000000000000 : ℝ)*(upper2) + (99755013/100000000000000 : ℝ)*(upper4) + (5548933/20000000000000 : ℝ)*(upper5) + (3863013791155703/100000000000000 : ℝ)*(major0) + (3863013791155703/100000000000000 : ℝ)*(major1) + (3863013791155703/100000000000000 : ℝ)*(major2) + (5073545010094923/100000000000000 : ℝ)*(sp0) + (202934069428773/4000000000000 : ℝ)*(sp1) + (5073423059873843/100000000000000 : ℝ)*(sp2) + (2632732443993879/100000000000000 : ℝ)*(sp3) + (211557070019/100000000000000 : ℝ)*(sp9) + (140232915501/100000000000000 : ℝ)*(sp10) + (18282694421/100000000000000 : ℝ)*(sp12) + (2632732443993879/100000000000000 : ℝ)*(f.failure) + (158548852899667/3125000000000 : ℝ)*(f.sum) + (24342304297427/14005000000000000000000000000 : ℝ)*base65 + (2077866064142624377/1400500000000000000000000000000000 : ℝ)*base68 + (2087831594990124377/1400500000000000000000000000000000 : ℝ)*base70 + (15393805144097875623/1400500000000000000000000000000000 : ℝ)*base71 + (75704213573333/14005000000000000000000000000 : ℝ)*base74 + (3054945610422375623/1400500000000000000000000000000000 : ℝ)*base75 + (2242772191361624377/1400500000000000000000000000000000 : ℝ)*base78 + (2474472154487375623/1400500000000000000000000000000000 : ℝ)*base79 + (16593181622121/7002500000000000000000000000 : ℝ)*base81 + (2612599/312500000000000000000 : ℝ)*base90 + (2612599/312500000000000000000 : ℝ)*base92 + (2612599/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (15873/20000 : ℝ) ≤ (34735699762573230708036865231737/43765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195616881/100000000000000 : ℝ)*(lower3) + (201119833/50000000000000 : ℝ)*(upper4) + (33630561/100000000000000 : ℝ)*(lower5) + (541412033227419/12500000000000 : ℝ)*(major0) + (541412033227419/12500000000000 : ℝ)*(major1) + (541412033227419/12500000000000 : ℝ)*(major2) + (5350842203/100000000000000 : ℝ)*(sp0) + (541784129637/100000000000000 : ℝ)*(sp1) + (427885599047/100000000000000 : ℝ)*(sp2) + (127992776409/50000000000000 : ℝ)*(sp3) + (5684253650132857/100000000000000 : ℝ)*(sp8) + (2841858608422711/50000000000000 : ℝ)*(sp9) + (1420957778844003/25000000000000 : ℝ)*(sp10) + (737905424642561/25000000000000 : ℝ)*(sp11) + (1475938842061531/50000000000000 : ℝ)*(f.failure) + (5684259000975059/100000000000000 : ℝ)*(f.sum) + (604775737799/437656250000000000000000000 : ℝ)*base65 + (1237137118454114421/175062500000000000000000000000000 : ℝ)*base68 + (976368306785114421/175062500000000000000000000000000 : ℝ)*base70 + (670679540781385579/175062500000000000000000000000000 : ℝ)*base71 + (81548562304207/14005000000000000000000000000 : ℝ)*base74 + (387645637829426921/175062500000000000000000000000000 : ℝ)*base76 + (920107022167801921/175062500000000000000000000000000 : ℝ)*base78 + (1282402826356739421/175062500000000000000000000000000 : ℝ)*base80 + (52936268203967/14005000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (236611/156250000000000000000 : ℝ)*base90 + (236611/156250000000000000000 : ℝ)*base92 + (236611/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82803/100000 : ℝ) ≤ (-144952173125809929523431482696433/175062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (243417237/100000000000000 : ℝ)*(lower0) + (3047023/50000000000000 : ℝ)*(upper1) + (1808473/10000000000000 : ℝ)*(upper3) + (107176473/50000000000000 : ℝ)*(upper5) + (1091357687906129/25000000000000 : ℝ)*(major0) + (1091357687906129/25000000000000 : ℝ)*(major1) + (1091357687906129/25000000000000 : ℝ)*(major2) + (22342043/1250000000000 : ℝ)*(sp4) + (142473027507/100000000000000 : ℝ)*(sp5) + (1216178999/10000000000000 : ℝ)*(sp7) + (1445829669461479/25000000000000 : ℝ)*(sp12) + (5783177992181849/100000000000000 : ℝ)*(sp13) + (1445830116302339/25000000000000 : ℝ)*(sp14) + (1487564478408143/50000000000000 : ℝ)*(sp15) + (743785279651569/25000000000000 : ℝ)*(f.failure) + (1445830116302339/25000000000000 : ℝ)*(f.sum) + (2444032711243/1750625000000000000000000000 : ℝ)*base65 + (134138995315661311/350125000000000000000000000000000 : ℝ)*base68 + (10040985685200338689/350125000000000000000000000000000 : ℝ)*base69 + (630046246717411311/350125000000000000000000000000000 : ℝ)*base72 + (452766649434929/14005000000000000000000000000 : ℝ)*base73 + (20088195875149661311/350125000000000000000000000000000 : ℝ)*base76 + (1437364790331161311/350125000000000000000000000000000 : ℝ)*base78 + (10479054719970838689/350125000000000000000000000000000 : ℝ)*base79 + (12427603515149/3501250000000000000000000000 : ℝ)*base82 + (409489/78125000000000000000 : ℝ)*base90 + (409489/78125000000000000000 : ℝ)*base92 + (409489/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1001_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4585319/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59193/100000 : ℝ) else (15873/20000 : ℝ) ≤ X j i ∧ X j i ≤ (82803/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1001_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8193/2048 : ℝ) ≤ p) (hpb : p ≤ (4097/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4585319/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59193/100000 : ℝ) else (15873/20000 : ℝ) ≤ X j i ∧ X j i ≤ (82803/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1001_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
