-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:01:29.759337+00:00
-- url     : https://prove2.me/submissions/d181956c-32c7-4a7c-8e2c-0a4eb55b99c9

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
theorem support_rectangle_w1012_box_0 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099279473/10000000000 : ℝ)*x 0 + (2689042523/5000000000 : ℝ)*x 1 + (672260677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099279473/10000000000 : ℝ)^8205 ≤ (2498048152553/20000000000000 : ℝ)^6157 := by
    have hnat : (2099279473 : ℕ)^8205*20000000000000^6157 ≤ 2498048152553^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099279473 10000000000 2498048152553 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689042523/5000000000 : ℝ)^8205 ≤ (21877438803983/50000000000000 : ℝ)^6157 := by
    have hnat : (2689042523 : ℕ)^8205*50000000000000^6157 ≤ 21877438803983^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689042523 5000000000 21877438803983 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672260677/1250000000 : ℝ)^8205 ≤ (8750976323899/20000000000000 : ℝ)^6157 := by
    have hnat : (672260677 : ℕ)^8205*20000000000000^6157 ≤ 8750976323899^6157*1250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672260677 1250000000 8750976323899 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099279473/10000000000 : ℝ), (2689042523/5000000000 : ℝ), (672260677/1250000000 : ℝ)] ![(2498048152553/20000000000000 : ℝ), (21877438803983/50000000000000 : ℝ), (8750976323899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099279473/10000000000 : ℝ)|^8205 ≤ (2498048152553/20000000000000 : ℝ)^6157
        have hw : |(-2099279473/10000000000 : ℝ)|=(2099279473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689042523/5000000000 : ℝ)|^8205 ≤ (21877438803983/50000000000000 : ℝ)^6157
        have hw : |(2689042523/5000000000 : ℝ)|=(2689042523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672260677/1250000000 : ℝ)|^8205 ≤ (8750976323899/20000000000000 : ℝ)^6157
        have hw : |(672260677/1250000000 : ℝ)|=(672260677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_1 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294555371/10000000000 : ℝ)*x 0 + (-2212204561/10000000000 : ℝ)*x 1 + (1075617021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294555371/10000000000 : ℝ)^8205 ≤ (42851598770963/100000000000000 : ℝ)^6157 := by
    have hnat : (5294555371 : ℕ)^8205*100000000000000^6157 ≤ 42851598770963^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294555371 10000000000 42851598770963 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212204561/10000000000 : ℝ)^8205 ≤ (13393522977031/100000000000000 : ℝ)^6157 := by
    have hnat : (2212204561 : ℕ)^8205*100000000000000^6157 ≤ 13393522977031^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212204561 10000000000 13393522977031 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075617021/2000000000 : ℝ)^8205 ≤ (21877439123821/50000000000000 : ℝ)^6157 := by
    have hnat : (1075617021 : ℕ)^8205*50000000000000^6157 ≤ 21877439123821^6157*2000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075617021 2000000000 21877439123821 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294555371/10000000000 : ℝ), (-2212204561/10000000000 : ℝ), (1075617021/2000000000 : ℝ)] ![(42851598770963/100000000000000 : ℝ), (13393522977031/100000000000000 : ℝ), (21877439123821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294555371/10000000000 : ℝ)|^8205 ≤ (42851598770963/100000000000000 : ℝ)^6157
        have hw : |(5294555371/10000000000 : ℝ)|=(5294555371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212204561/10000000000 : ℝ)|^8205 ≤ (13393522977031/100000000000000 : ℝ)^6157
        have hw : |(-2212204561/10000000000 : ℝ)|=(2212204561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075617021/2000000000 : ℝ)|^8205 ≤ (21877439123821/50000000000000 : ℝ)^6157
        have hw : |(1075617021/2000000000 : ℝ)|=(1075617021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_2 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647277683/5000000000 : ℝ)*x 0 + (1344521213/2500000000 : ℝ)*x 1 + (-1106102453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647277683/5000000000 : ℝ)^8205 ≤ (8570319743407/20000000000000 : ℝ)^6157 := by
    have hnat : (2647277683 : ℕ)^8205*20000000000000^6157 ≤ 8570319743407^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647277683 5000000000 8570319743407 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344521213/2500000000 : ℝ)^8205 ≤ (43754875504623/100000000000000 : ℝ)^6157 := by
    have hnat : (1344521213 : ℕ)^8205*100000000000000^6157 ≤ 43754875504623^6157*2500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344521213 2500000000 43754875504623 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106102453/5000000000 : ℝ)^8205 ≤ (535741030423/4000000000000 : ℝ)^6157 := by
    have hnat : (1106102453 : ℕ)^8205*4000000000000^6157 ≤ 535741030423^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106102453 5000000000 535741030423 4000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647277683/5000000000 : ℝ), (1344521213/2500000000 : ℝ), (-1106102453/5000000000 : ℝ)] ![(8570319743407/20000000000000 : ℝ), (43754875504623/100000000000000 : ℝ), (535741030423/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647277683/5000000000 : ℝ)|^8205 ≤ (8570319743407/20000000000000 : ℝ)^6157
        have hw : |(2647277683/5000000000 : ℝ)|=(2647277683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344521213/2500000000 : ℝ)|^8205 ≤ (43754875504623/100000000000000 : ℝ)^6157
        have hw : |(1344521213/2500000000 : ℝ)|=(1344521213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106102453/5000000000 : ℝ)|^8205 ≤ (535741030423/4000000000000 : ℝ)^6157
        have hw : |(-1106102453/5000000000 : ℝ)|=(1106102453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_3 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2246169221/5000000000 : ℝ)*x 0 + (34648079/80000000 : ℝ)*x 1 + (2165504833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246169221/5000000000 : ℝ)^8205 ≤ (17212523769003/50000000000000 : ℝ)^6157 := by
    have hnat : (2246169221 : ℕ)^8205*50000000000000^6157 ≤ 17212523769003^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246169221 5000000000 17212523769003 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34648079/80000000 : ℝ)^8205 ≤ (16393738639569/50000000000000 : ℝ)^6157 := by
    have hnat : (34648079 : ℕ)^8205*50000000000000^6157 ≤ 16393738639569^6157*80000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34648079 80000000 16393738639569 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165504833/5000000000 : ℝ)^8205 ≤ (32787475170633/100000000000000 : ℝ)^6157 := by
    have hnat : (2165504833 : ℕ)^8205*100000000000000^6157 ≤ 32787475170633^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165504833 5000000000 32787475170633 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246169221/5000000000 : ℝ), (34648079/80000000 : ℝ), (2165504833/5000000000 : ℝ)] ![(17212523769003/50000000000000 : ℝ), (16393738639569/50000000000000 : ℝ), (32787475170633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246169221/5000000000 : ℝ)|^8205 ≤ (17212523769003/50000000000000 : ℝ)^6157
        have hw : |(2246169221/5000000000 : ℝ)|=(2246169221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34648079/80000000 : ℝ)|^8205 ≤ (16393738639569/50000000000000 : ℝ)^6157
        have hw : |(34648079/80000000 : ℝ)|=(34648079/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165504833/5000000000 : ℝ)|^8205 ≤ (32787475170633/100000000000000 : ℝ)^6157
        have hw : |(2165504833/5000000000 : ℝ)|=(2165504833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_4 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1181693369/5000000000 : ℝ)*x 0 + (5279242767/10000000000 : ℝ)*x 1 + (5279242791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1181693369/5000000000 : ℝ)^8205 ≤ (14626956467689/100000000000000 : ℝ)^6157 := by
    have hnat : (1181693369 : ℕ)^8205*100000000000000^6157 ≤ 14626956467689^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181693369 5000000000 14626956467689 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279242767/10000000000 : ℝ)^8205 ≤ (10671630407801/25000000000000 : ℝ)^6157 := by
    have hnat : (5279242767 : ℕ)^8205*25000000000000^6157 ≤ 10671630407801^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279242767 10000000000 10671630407801 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279242791/10000000000 : ℝ)^8205 ≤ (4268652188981/10000000000000 : ℝ)^6157 := by
    have hnat : (5279242791 : ℕ)^8205*10000000000000^6157 ≤ 4268652188981^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279242791 10000000000 4268652188981 10000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1181693369/5000000000 : ℝ), (5279242767/10000000000 : ℝ), (5279242791/10000000000 : ℝ)] ![(14626956467689/100000000000000 : ℝ), (10671630407801/25000000000000 : ℝ), (4268652188981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1181693369/5000000000 : ℝ)|^8205 ≤ (14626956467689/100000000000000 : ℝ)^6157
        have hw : |(-1181693369/5000000000 : ℝ)|=(1181693369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279242767/10000000000 : ℝ)|^8205 ≤ (10671630407801/25000000000000 : ℝ)^6157
        have hw : |(5279242767/10000000000 : ℝ)|=(5279242767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279242791/10000000000 : ℝ)|^8205 ≤ (4268652188981/10000000000000 : ℝ)^6157
        have hw : |(5279242791/10000000000 : ℝ)|=(5279242791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_5 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107291903/200000000 : ℝ)*x 0 + (-2250674443/10000000000 : ℝ)*x 1 + (65990529/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107291903/200000000 : ℝ)^8205 ≤ (43608681595289/100000000000000 : ℝ)^6157 := by
    have hnat : (107291903 : ℕ)^8205*100000000000000^6157 ≤ 43608681595289^6157*200000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107291903 200000000 43608681595289 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250674443/10000000000 : ℝ)^8205 ≤ (6852400789531/50000000000000 : ℝ)^6157 := by
    have hnat : (2250674443 : ℕ)^8205*50000000000000^6157 ≤ 6852400789531^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250674443 10000000000 6852400789531 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65990529/125000000 : ℝ)^8205 ≤ (42686516814653/100000000000000 : ℝ)^6157 := by
    have hnat : (65990529 : ℕ)^8205*100000000000000^6157 ≤ 42686516814653^6157*125000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65990529 125000000 42686516814653 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107291903/200000000 : ℝ), (-2250674443/10000000000 : ℝ), (65990529/125000000 : ℝ)] ![(43608681595289/100000000000000 : ℝ), (6852400789531/50000000000000 : ℝ), (42686516814653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107291903/200000000 : ℝ)|^8205 ≤ (43608681595289/100000000000000 : ℝ)^6157
        have hw : |(107291903/200000000 : ℝ)|=(107291903/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250674443/10000000000 : ℝ)|^8205 ≤ (6852400789531/50000000000000 : ℝ)^6157
        have hw : |(-2250674443/10000000000 : ℝ)|=(2250674443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65990529/125000000 : ℝ)|^8205 ≤ (42686516814653/100000000000000 : ℝ)^6157
        have hw : |(65990529/125000000 : ℝ)|=(65990529/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_6 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134114863/250000000 : ℝ)*x 0 + (1319810767/2500000000 : ℝ)*x 1 + (-2250674291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134114863/250000000 : ℝ)^8205 ≤ (43608674770551/100000000000000 : ℝ)^6157 := by
    have hnat : (134114863 : ℕ)^8205*100000000000000^6157 ≤ 43608674770551^6157*250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134114863 250000000 43608674770551 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319810767/2500000000 : ℝ)^8205 ≤ (42686524874563/100000000000000 : ℝ)^6157 := by
    have hnat : (1319810767 : ℕ)^8205*100000000000000^6157 ≤ 42686524874563^6157*2500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319810767 2500000000 42686524874563 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250674291/10000000000 : ℝ)^8205 ≤ (3426200086409/25000000000000 : ℝ)^6157 := by
    have hnat : (2250674291 : ℕ)^8205*25000000000000^6157 ≤ 3426200086409^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250674291 10000000000 3426200086409 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134114863/250000000 : ℝ), (1319810767/2500000000 : ℝ), (-2250674291/10000000000 : ℝ)] ![(43608674770551/100000000000000 : ℝ), (42686524874563/100000000000000 : ℝ), (3426200086409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134114863/250000000 : ℝ)|^8205 ≤ (43608674770551/100000000000000 : ℝ)^6157
        have hw : |(134114863/250000000 : ℝ)|=(134114863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319810767/2500000000 : ℝ)|^8205 ≤ (42686524874563/100000000000000 : ℝ)^6157
        have hw : |(1319810767/2500000000 : ℝ)|=(1319810767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2250674291/10000000000 : ℝ)|^8205 ≤ (3426200086409/25000000000000 : ℝ)^6157
        have hw : |(-2250674291/10000000000 : ℝ)|=(2250674291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_7 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4273990743/10000000000 : ℝ)*x 0 + (88803233/200000000 : ℝ)*x 1 + (2220080863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273990743/10000000000 : ℝ)^8205 ≤ (16106750405529/50000000000000 : ℝ)^6157 := by
    have hnat : (4273990743 : ℕ)^8205*50000000000000^6157 ≤ 16106750405529^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273990743 10000000000 16106750405529 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88803233/200000000 : ℝ)^8205 ≤ (3389324920207/10000000000000 : ℝ)^6157 := by
    have hnat : (88803233 : ℕ)^8205*10000000000000^6157 ≤ 3389324920207^6157*200000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88803233 200000000 3389324920207 10000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220080863/5000000000 : ℝ)^8205 ≤ (16946624987587/50000000000000 : ℝ)^6157 := by
    have hnat : (2220080863 : ℕ)^8205*50000000000000^6157 ≤ 16946624987587^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220080863 5000000000 16946624987587 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273990743/10000000000 : ℝ), (88803233/200000000 : ℝ), (2220080863/5000000000 : ℝ)] ![(16106750405529/50000000000000 : ℝ), (3389324920207/10000000000000 : ℝ), (16946624987587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273990743/10000000000 : ℝ)|^8205 ≤ (16106750405529/50000000000000 : ℝ)^6157
        have hw : |(4273990743/10000000000 : ℝ)|=(4273990743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88803233/200000000 : ℝ)|^8205 ≤ (3389324920207/10000000000000 : ℝ)^6157
        have hw : |(88803233/200000000 : ℝ)|=(88803233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220080863/5000000000 : ℝ)|^8205 ≤ (16946624987587/50000000000000 : ℝ)^6157
        have hw : |(2220080863/5000000000 : ℝ)|=(2220080863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_8 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1154161563/5000000000 : ℝ)*x 0 + (1042456057/2000000000 : ℝ)*x 1 + (5387677511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1154161563/5000000000 : ℝ)^8205 ≤ (14174581731103/100000000000000 : ℝ)^6157 := by
    have hnat : (1154161563 : ℕ)^8205*100000000000000^6157 ≤ 14174581731103^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154161563 5000000000 14174581731103 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042456057/2000000000 : ℝ)^8205 ≤ (20983254290443/50000000000000 : ℝ)^6157 := by
    have hnat : (1042456057 : ℕ)^8205*50000000000000^6157 ≤ 20983254290443^6157*2000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042456057 2000000000 20983254290443 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387677511/10000000000 : ℝ)^8205 ≤ (21929454836921/50000000000000 : ℝ)^6157 := by
    have hnat : (5387677511 : ℕ)^8205*50000000000000^6157 ≤ 21929454836921^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387677511 10000000000 21929454836921 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1154161563/5000000000 : ℝ), (1042456057/2000000000 : ℝ), (5387677511/10000000000 : ℝ)] ![(14174581731103/100000000000000 : ℝ), (20983254290443/50000000000000 : ℝ), (21929454836921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1154161563/5000000000 : ℝ)|^8205 ≤ (14174581731103/100000000000000 : ℝ)^6157
        have hw : |(-1154161563/5000000000 : ℝ)|=(1154161563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042456057/2000000000 : ℝ)|^8205 ≤ (20983254290443/50000000000000 : ℝ)^6157
        have hw : |(1042456057/2000000000 : ℝ)|=(1042456057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387677511/10000000000 : ℝ)|^8205 ≤ (21929454836921/50000000000000 : ℝ)^6157
        have hw : |(5387677511/10000000000 : ℝ)|=(5387677511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_9 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528775447/1000000000 : ℝ)*x 0 + (-88335989/400000000 : ℝ)*x 1 + (2693838511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528775447/1000000000 : ℝ)^8205 ≤ (42778262199241/100000000000000 : ℝ)^6157 := by
    have hnat : (528775447 : ℕ)^8205*100000000000000^6157 ≤ 42778262199241^6157*1000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528775447 1000000000 42778262199241 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88335989/400000000 : ℝ)^8205 ≤ (835177088739/6250000000000 : ℝ)^6157 := by
    have hnat : (88335989 : ℕ)^8205*6250000000000^6157 ≤ 835177088739^6157*400000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88335989 400000000 835177088739 6250000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693838511/5000000000 : ℝ)^8205 ≤ (21929452184487/50000000000000 : ℝ)^6157 := by
    have hnat : (2693838511 : ℕ)^8205*50000000000000^6157 ≤ 21929452184487^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693838511 5000000000 21929452184487 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528775447/1000000000 : ℝ), (-88335989/400000000 : ℝ), (2693838511/5000000000 : ℝ)] ![(42778262199241/100000000000000 : ℝ), (835177088739/6250000000000 : ℝ), (21929452184487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528775447/1000000000 : ℝ)|^8205 ≤ (42778262199241/100000000000000 : ℝ)^6157
        have hw : |(528775447/1000000000 : ℝ)|=(528775447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88335989/400000000 : ℝ)|^8205 ≤ (835177088739/6250000000000 : ℝ)^6157
        have hw : |(-88335989/400000000 : ℝ)|=(88335989/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693838511/5000000000 : ℝ)|^8205 ≤ (21929452184487/50000000000000 : ℝ)^6157
        have hw : |(2693838511/5000000000 : ℝ)|=(2693838511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_10 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105755087/200000000 : ℝ)*x 0 + (5387676877/10000000000 : ℝ)*x 1 + (-2208400081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105755087/200000000 : ℝ)^8205 ≤ (21389130452757/50000000000000 : ℝ)^6157 := by
    have hnat : (105755087 : ℕ)^8205*50000000000000^6157 ≤ 21389130452757^6157*200000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105755087 200000000 21389130452757 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387676877/10000000000 : ℝ)^8205 ≤ (43858902795957/100000000000000 : ℝ)^6157 := by
    have hnat : (5387676877 : ℕ)^8205*100000000000000^6157 ≤ 43858902795957^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387676877 10000000000 43858902795957 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208400081/10000000000 : ℝ)^8205 ≤ (6681418145237/50000000000000 : ℝ)^6157 := by
    have hnat : (2208400081 : ℕ)^8205*50000000000000^6157 ≤ 6681418145237^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208400081 10000000000 6681418145237 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105755087/200000000 : ℝ), (5387676877/10000000000 : ℝ), (-2208400081/10000000000 : ℝ)] ![(21389130452757/50000000000000 : ℝ), (43858902795957/100000000000000 : ℝ), (6681418145237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105755087/200000000 : ℝ)|^8205 ≤ (21389130452757/50000000000000 : ℝ)^6157
        have hw : |(105755087/200000000 : ℝ)|=(105755087/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387676877/10000000000 : ℝ)|^8205 ≤ (43858902795957/100000000000000 : ℝ)^6157
        have hw : |(5387676877/10000000000 : ℝ)|=(5387676877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208400081/10000000000 : ℝ)|^8205 ≤ (6681418145237/50000000000000 : ℝ)^6157
        have hw : |(-2208400081/10000000000 : ℝ)|=(2208400081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_11 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4513253769/10000000000 : ℝ)*x 0 + (2160205517/5000000000 : ℝ)*x 1 + (216020609/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4513253769/10000000000 : ℝ)^8205 ≤ (17319400210067/50000000000000 : ℝ)^6157 := by
    have hnat : (4513253769 : ℕ)^8205*50000000000000^6157 ≤ 17319400210067^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513253769 10000000000 17319400210067 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160205517/5000000000 : ℝ)^8205 ≤ (6536118801193/20000000000000 : ℝ)^6157 := by
    have hnat : (2160205517 : ℕ)^8205*20000000000000^6157 ≤ 6536118801193^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160205517 5000000000 6536118801193 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216020609/500000000 : ℝ)^8205 ≤ (8170151389503/25000000000000 : ℝ)^6157 := by
    have hnat : (216020609 : ℕ)^8205*25000000000000^6157 ≤ 8170151389503^6157*500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216020609 500000000 8170151389503 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4513253769/10000000000 : ℝ), (2160205517/5000000000 : ℝ), (216020609/500000000 : ℝ)] ![(17319400210067/50000000000000 : ℝ), (6536118801193/20000000000000 : ℝ), (8170151389503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4513253769/10000000000 : ℝ)|^8205 ≤ (17319400210067/50000000000000 : ℝ)^6157
        have hw : |(4513253769/10000000000 : ℝ)|=(4513253769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2160205517/5000000000 : ℝ)|^8205 ≤ (6536118801193/20000000000000 : ℝ)^6157
        have hw : |(2160205517/5000000000 : ℝ)|=(2160205517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216020609/500000000 : ℝ)|^8205 ≤ (8170151389503/25000000000000 : ℝ)^6157
        have hw : |(216020609/500000000 : ℝ)|=(216020609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_12 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-538687299/2500000000 : ℝ)*x 0 + (5443668183/10000000000 : ℝ)*x 1 + (2635636211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538687299/2500000000 : ℝ)^8205 ≤ (6465986598391/50000000000000 : ℝ)^6157 := by
    have hnat : (538687299 : ℕ)^8205*50000000000000^6157 ≤ 6465986598391^6157*2500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538687299 2500000000 6465986598391 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443668183/10000000000 : ℝ)^8205 ≤ (22233683141721/50000000000000 : ℝ)^6157 := by
    have hnat : (5443668183 : ℕ)^8205*50000000000000^6157 ≤ 22233683141721^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443668183 10000000000 22233683141721 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635636211/5000000000 : ℝ)^8205 ≤ (4260066050379/10000000000000 : ℝ)^6157 := by
    have hnat : (2635636211 : ℕ)^8205*10000000000000^6157 ≤ 4260066050379^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635636211 5000000000 4260066050379 10000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538687299/2500000000 : ℝ), (5443668183/10000000000 : ℝ), (2635636211/5000000000 : ℝ)] ![(6465986598391/50000000000000 : ℝ), (22233683141721/50000000000000 : ℝ), (4260066050379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538687299/2500000000 : ℝ)|^8205 ≤ (6465986598391/50000000000000 : ℝ)^6157
        have hw : |(-538687299/2500000000 : ℝ)|=(538687299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443668183/10000000000 : ℝ)|^8205 ≤ (22233683141721/50000000000000 : ℝ)^6157
        have hw : |(5443668183/10000000000 : ℝ)|=(5443668183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635636211/5000000000 : ℝ)|^8205 ≤ (4260066050379/10000000000000 : ℝ)^6157
        have hw : |(2635636211/5000000000 : ℝ)|=(2635636211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_13 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268512003/500000000 : ℝ)*x 0 + (-1126858333/5000000000 : ℝ)*x 1 + (1317818167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268512003/500000000 : ℝ)^8205 ≤ (43669843138889/100000000000000 : ℝ)^6157 := by
    have hnat : (268512003 : ℕ)^8205*100000000000000^6157 ≤ 43669843138889^6157*500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268512003 500000000 43669843138889 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126858333/5000000000 : ℝ)^8205 ≤ (858093355349/6250000000000 : ℝ)^6157 := by
    have hnat : (1126858333 : ℕ)^8205*6250000000000^6157 ≤ 858093355349^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126858333 5000000000 858093355349 6250000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317818167/2500000000 : ℝ)^8205 ≤ (42600663153177/100000000000000 : ℝ)^6157 := by
    have hnat : (1317818167 : ℕ)^8205*100000000000000^6157 ≤ 42600663153177^6157*2500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317818167 2500000000 42600663153177 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268512003/500000000 : ℝ), (-1126858333/5000000000 : ℝ), (1317818167/2500000000 : ℝ)] ![(43669843138889/100000000000000 : ℝ), (858093355349/6250000000000 : ℝ), (42600663153177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268512003/500000000 : ℝ)|^8205 ≤ (43669843138889/100000000000000 : ℝ)^6157
        have hw : |(268512003/500000000 : ℝ)|=(268512003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126858333/5000000000 : ℝ)|^8205 ≤ (858093355349/6250000000000 : ℝ)^6157
        have hw : |(-1126858333/5000000000 : ℝ)|=(1126858333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317818167/2500000000 : ℝ)|^8205 ≤ (42600663153177/100000000000000 : ℝ)^6157
        have hw : |(1317818167/2500000000 : ℝ)|=(1317818167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_14 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074048003/2000000000 : ℝ)*x 0 + (5271272611/10000000000 : ℝ)*x 1 + (-1126858401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074048003/2000000000 : ℝ)^8205 ≤ (43669842651237/100000000000000 : ℝ)^6157 := by
    have hnat : (1074048003 : ℕ)^8205*100000000000000^6157 ≤ 43669842651237^6157*2000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074048003 2000000000 43669842651237 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271272611/10000000000 : ℝ)^8205 ≤ (8520132507859/20000000000000 : ℝ)^6157 := by
    have hnat : (5271272611 : ℕ)^8205*20000000000000^6157 ≤ 8520132507859^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271272611 10000000000 8520132507859 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126858401/5000000000 : ℝ)^8205 ≤ (1716186848709/12500000000000 : ℝ)^6157 := by
    have hnat : (1126858401 : ℕ)^8205*12500000000000^6157 ≤ 1716186848709^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126858401 5000000000 1716186848709 12500000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074048003/2000000000 : ℝ), (5271272611/10000000000 : ℝ), (-1126858401/5000000000 : ℝ)] ![(43669842651237/100000000000000 : ℝ), (8520132507859/20000000000000 : ℝ), (1716186848709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074048003/2000000000 : ℝ)|^8205 ≤ (43669842651237/100000000000000 : ℝ)^6157
        have hw : |(1074048003/2000000000 : ℝ)|=(1074048003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271272611/10000000000 : ℝ)|^8205 ≤ (8520132507859/20000000000000 : ℝ)^6157
        have hw : |(5271272611/10000000000 : ℝ)|=(5271272611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126858401/5000000000 : ℝ)|^8205 ≤ (1716186848709/12500000000000 : ℝ)^6157
        have hw : |(-1126858401/5000000000 : ℝ)|=(1126858401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_box_15 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4256155037/10000000000 : ℝ)*x 0 + (2224479123/5000000000 : ℝ)*x 1 + (4448957949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256155037/10000000000 : ℝ)^8205 ≤ (16017240255857/50000000000000 : ℝ)^6157 := by
    have hnat : (4256155037 : ℕ)^8205*50000000000000^6157 ≤ 16017240255857^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256155037 10000000000 16017240255857 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224479123/5000000000 : ℝ)^8205 ≤ (4247845156739/12500000000000 : ℝ)^6157 := by
    have hnat : (2224479123 : ℕ)^8205*12500000000000^6157 ≤ 4247845156739^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224479123 5000000000 4247845156739 12500000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4448957949/10000000000 : ℝ)^8205 ≤ (8495689557679/25000000000000 : ℝ)^6157 := by
    have hnat : (4448957949 : ℕ)^8205*25000000000000^6157 ≤ 8495689557679^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448957949 10000000000 8495689557679 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256155037/10000000000 : ℝ), (2224479123/5000000000 : ℝ), (4448957949/10000000000 : ℝ)] ![(16017240255857/50000000000000 : ℝ), (4247845156739/12500000000000 : ℝ), (8495689557679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256155037/10000000000 : ℝ)|^8205 ≤ (16017240255857/50000000000000 : ℝ)^6157
        have hw : |(4256155037/10000000000 : ℝ)|=(4256155037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2224479123/5000000000 : ℝ)|^8205 ≤ (4247845156739/12500000000000 : ℝ)^6157
        have hw : |(2224479123/5000000000 : ℝ)|=(2224479123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4448957949/10000000000 : ℝ)|^8205 ≤ (8495689557679/25000000000000 : ℝ)^6157
        have hw : |(4448957949/10000000000 : ℝ)|=(4448957949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1012_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59201/100000 : ℝ) ∧ (79401/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20707/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (873/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1397/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (873/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1397/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (873/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1397/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (873/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1397/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (873/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1397/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (873/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1397/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1397/12500 : ℝ) ^ (2051/512 : ℝ) ≤ (3080343303234431/20000000000000000000 : ℝ) := by
    have hpowers : (1397/12500 : ℝ)^2051 ≤ (3080343303234431/20000000000000000000 : ℝ)^512 := by
      have hnat : (1397 : ℕ)^2051*20000000000000000000^512 ≤ 3080343303234431^512*12500^2051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1397 12500 3080343303234431 20000000000000000000 2051 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1397/12500 : ℝ)) (X := (3080343303234431/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hpowhi : (873/6250 : ℝ) ^ (2051/512 : ℝ) ≤ (37629454824161759/100000000000000000000 : ℝ) := by
    have hpowers : (873/6250 : ℝ)^2051 ≤ (37629454824161759/100000000000000000000 : ℝ)^512 := by
      have hnat : (873 : ℕ)^2051*100000000000000000000^512 ≤ 37629454824161759^512*6250^2051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        873 6250 37629454824161759 100000000000000000000 2051 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (873/6250 : ℝ)) (X := (37629454824161759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003080343303234431/10000000000000000000 : ℝ) ≤ (2500192217642089/2500000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (10003080343303234431/10000000000000000000 : ℝ)^512 ≤ (2500192217642089/2500000000000000 : ℝ)^2051 := by
      have hnat : (10003080343303234431 : ℕ)^512*2500000000000000^2051 ≤ 2500192217642089^2051*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003080343303234431 10000000000000000000 2500192217642089 2500000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500192217642089/2500000000000000 : ℝ)) (X := (10003080343303234431/10000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026515585670166957/50000000000000000000 : ℝ) ≤ (2500330894187453/2500000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (50026515585670166957/50000000000000000000 : ℝ)^512 ≤ (2500330894187453/2500000000000000 : ℝ)^2051 := by
      have hnat : (50026515585670166957 : ℕ)^512*2500000000000000^2051 ≤ 2500330894187453^2051*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026515585670166957 50000000000000000000 2500330894187453 2500000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500330894187453/2500000000000000 : ℝ)) (X := (50026515585670166957/50000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037629454824161759/50000000000000000000 : ℝ) ≤ (2500469570732817/2500000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (50037629454824161759/50000000000000000000 : ℝ)^512 ≤ (2500469570732817/2500000000000000 : ℝ)^2051 := by
      have hnat : (50037629454824161759 : ℕ)^512*2500000000000000^2051 ≤ 2500469570732817^2051*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037629454824161759 50000000000000000000 2500469570732817 2500000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500469570732817/2500000000000000 : ℝ)) (X := (50037629454824161759/50000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3080343303234431/20000000000000000000 : ℝ) ≤ ((174435924337868409/174500000000000000 : ℝ)+2*(34669136341/17450000000000 : ℝ)*(1397/12500 : ℝ))^(2051/512 : ℝ) := by
    rw [show (174435924337868409/174500000000000000 : ℝ)+2*(34669136341/17450000000000 : ℝ)*(1397/12500 : ℝ)=(2500192217642089/2500000000000000 : ℝ) by norm_num, show 1+2*(3080343303234431/20000000000000000000 : ℝ)=(10003080343303234431/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37629454824161759/100000000000000000000 : ℝ)+(3080343303234431/20000000000000000000 : ℝ) ≤ ((174435924337868409/174500000000000000 : ℝ)+(34669136341/17450000000000 : ℝ)*((873/6250 : ℝ)+(1397/12500 : ℝ)))^(2051/512 : ℝ) := by
    rw [show (174435924337868409/174500000000000000 : ℝ)+(34669136341/17450000000000 : ℝ)*((873/6250 : ℝ)+(1397/12500 : ℝ))=(2500330894187453/2500000000000000 : ℝ) by norm_num, show 1+(37629454824161759/100000000000000000000 : ℝ)+(3080343303234431/20000000000000000000 : ℝ)=(50026515585670166957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37629454824161759/100000000000000000000 : ℝ) ≤ ((174435924337868409/174500000000000000 : ℝ)+2*(34669136341/17450000000000 : ℝ)*(873/6250 : ℝ))^(2051/512 : ℝ) := by
    rw [show (174435924337868409/174500000000000000 : ℝ)+2*(34669136341/17450000000000 : ℝ)*(873/6250 : ℝ)=(2500469570732817/2500000000000000 : ℝ) by norm_num, show 1+2*(37629454824161759/100000000000000000000 : ℝ)=(50037629454824161759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (174435924337868409/174500000000000000 : ℝ)*(X 1 0+X 2 0)+(34669136341/17450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (873/6250 : ℝ)) (c := (174435924337868409/174500000000000000 : ℝ)) (alpha := (34669136341/17450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (174435924337868409/174500000000000000 : ℝ)*(X 0 1+X 2 1)+(34669136341/17450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (873/6250 : ℝ)) (c := (174435924337868409/174500000000000000 : ℝ)) (alpha := (34669136341/17450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (174435924337868409/174500000000000000 : ℝ)*(X 0 2+X 1 2)+(34669136341/17450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (873/6250 : ℝ)) (c := (174435924337868409/174500000000000000 : ℝ)) (alpha := (34669136341/17450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2099279473/10000000000 : ℝ)*X 0 0+(2689042523/5000000000 : ℝ)*X 0 1+(672260677/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294555371/10000000000 : ℝ)*X 1 0+(-2212204561/10000000000 : ℝ)*X 1 1+(1075617021/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647277683/5000000000 : ℝ)*X 2 0+(1344521213/2500000000 : ℝ)*X 2 1+(-1106102453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2246169221/5000000000 : ℝ)*X 0 0+(34648079/80000000 : ℝ)*X 0 1+(2165504833/5000000000 : ℝ)*X 0 2+(2246169221/5000000000 : ℝ)*X 1 0+(34648079/80000000 : ℝ)*X 1 1+(2165504833/5000000000 : ℝ)*X 1 2+(2246169221/5000000000 : ℝ)*X 2 0+(34648079/80000000 : ℝ)*X 2 1+(2165504833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1181693369/5000000000 : ℝ)*X 0 0+(5279242767/10000000000 : ℝ)*X 0 1+(5279242791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((107291903/200000000 : ℝ)*X 1 0+(-2250674443/10000000000 : ℝ)*X 1 1+(65990529/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((134114863/250000000 : ℝ)*X 2 0+(1319810767/2500000000 : ℝ)*X 2 1+(-2250674291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273990743/10000000000 : ℝ)*X 0 0+(88803233/200000000 : ℝ)*X 0 1+(2220080863/5000000000 : ℝ)*X 0 2+(4273990743/10000000000 : ℝ)*X 1 0+(88803233/200000000 : ℝ)*X 1 1+(2220080863/5000000000 : ℝ)*X 1 2+(4273990743/10000000000 : ℝ)*X 2 0+(88803233/200000000 : ℝ)*X 2 1+(2220080863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1154161563/5000000000 : ℝ)*X 0 0+(1042456057/2000000000 : ℝ)*X 0 1+(5387677511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528775447/1000000000 : ℝ)*X 1 0+(-88335989/400000000 : ℝ)*X 1 1+(2693838511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105755087/200000000 : ℝ)*X 2 0+(5387676877/10000000000 : ℝ)*X 2 1+(-2208400081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4513253769/10000000000 : ℝ)*X 0 0+(2160205517/5000000000 : ℝ)*X 0 1+(216020609/500000000 : ℝ)*X 0 2+(4513253769/10000000000 : ℝ)*X 1 0+(2160205517/5000000000 : ℝ)*X 1 1+(216020609/500000000 : ℝ)*X 1 2+(4513253769/10000000000 : ℝ)*X 2 0+(2160205517/5000000000 : ℝ)*X 2 1+(216020609/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-538687299/2500000000 : ℝ)*X 0 0+(5443668183/10000000000 : ℝ)*X 0 1+(2635636211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((268512003/500000000 : ℝ)*X 1 0+(-1126858333/5000000000 : ℝ)*X 1 1+(1317818167/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1074048003/2000000000 : ℝ)*X 2 0+(5271272611/10000000000 : ℝ)*X 2 1+(-1126858401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4256155037/10000000000 : ℝ)*X 0 0+(2224479123/5000000000 : ℝ)*X 0 1+(4448957949/10000000000 : ℝ)*X 0 2+(4256155037/10000000000 : ℝ)*X 1 0+(2224479123/5000000000 : ℝ)*X 1 1+(4448957949/10000000000 : ℝ)*X 1 2+(4256155037/10000000000 : ℝ)*X 2 0+(2224479123/5000000000 : ℝ)*X 2 1+(4448957949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-1357180776404073989408253419793/2181250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118820087/100000000000000 : ℝ)*(upper0) + (175654573/100000000000000 : ℝ)*(upper1) + (55858629/50000000000000 : ℝ)*(upper2) + (41617707/100000000000000 : ℝ)*(upper5) + (1905359110547991/50000000000000 : ℝ)*(major0) + (1905359110547991/50000000000000 : ℝ)*(major1) + (1905359110547991/50000000000000 : ℝ)*(major2) + (6287421591/100000000000000 : ℝ)*(sp1) + (1225482033/12500000000000 : ℝ)*(sp3) + (2524428870503939/50000000000000 : ℝ)*(sp4) + (315553215849143/6250000000000 : ℝ)*(sp5) + (1262142553238987/25000000000000 : ℝ)*(sp6) + (20260226599247/781250000000 : ℝ)*(sp7) + (28752805193/10000000000000 : ℝ)*(sp14) + (2593318808559879/100000000000000 : ℝ)*(f.failure) + (2524428870503939/50000000000000 : ℝ)*(f.sum) + (877228860027/218125000000000000000000000 : ℝ)*base66 + (25074043064776319/8725000000000000000000000000000 : ℝ)*base67 + (9586060547423681/8725000000000000000000000000000 : ℝ)*base70 + (77486534681198681/8725000000000000000000000000000 : ℝ)*base72 + (47106787053701/1745000000000000000000000000 : ℝ)*base74 + (7737256753248681/8725000000000000000000000000000 : ℝ)*base76 + (42974495723723681/8725000000000000000000000000000 : ℝ)*base78 + (25893387048523681/8725000000000000000000000000000 : ℝ)*base80 + (1629421010179/436250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7317177/2000000000000000000000 : ℝ)*base90 + (7317177/2000000000000000000000 : ℝ)*base92 + (7317177/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59201/100000 : ℝ) ≤ (2582754587167687437927674099823/4362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19173823/100000000000000 : ℝ)*(lower1) + (31669043/50000000000000 : ℝ)*(lower4) + (108140369/50000000000000 : ℝ)*(lower5) + (1936374345093117/50000000000000 : ℝ)*(major0) + (1936374345093117/50000000000000 : ℝ)*(major1) + (1936374345093117/50000000000000 : ℝ)*(major2) + (5090208199474141/100000000000000 : ℝ)*(sp0) + (5090224374196453/100000000000000 : ℝ)*(sp1) + (203608071833483/4000000000000 : ℝ)*(sp2) + (658881672092629/25000000000000 : ℝ)*(sp3) + (5913186181/100000000000000 : ℝ)*(sp5) + (5890104179/100000000000000 : ℝ)*(sp7) + (28491545559/100000000000000 : ℝ)*(sp10) + (22087908493/100000000000000 : ℝ)*(sp12) + (329441572309337/12500000000000 : ℝ)*(f.failure) + (2545115143691317/50000000000000 : ℝ)*(f.sum) + (394531818167/109062500000000000000000000 : ℝ)*base66 + (3364439554235853/8725000000000000000000000000000 : ℝ)*base67 + (110357249524410853/8725000000000000000000000000000 : ℝ)*base69 + (18268853386160853/8725000000000000000000000000000 : ℝ)*base71 + (7285295171121/872500000000000000000000000 : ℝ)*base74 + (131246602792735853/8725000000000000000000000000000 : ℝ)*base75 + (35295648247085853/8725000000000000000000000000000 : ℝ)*base77 + (66197933307685853/8725000000000000000000000000000 : ℝ)*base79 + (2722195894743/1745000000000000000000000000 : ℝ)*base81 + (2737369/250000000000000000000 : ℝ)*base89 + (2737369/250000000000000000000 : ℝ)*base91 + (2737369/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79401/100000 : ℝ) ≤ (69279125851623192886953064539/87250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17313577/5000000000000 : ℝ)*(upper0) + (37365239/25000000000000 : ℝ)*(upper2) + (150156477/100000000000000 : ℝ)*(lower3) + (315503671/100000000000000 : ℝ)*(lower5) + (86820087410857/2000000000000 : ℝ)*(major0) + (86820087410857/2000000000000 : ℝ)*(major1) + (86820087410857/2000000000000 : ℝ)*(major2) + (11916776089/10000000000000 : ℝ)*(sp1) + (11474584821/100000000000000 : ℝ)*(sp4) + (5701323478941169/100000000000000 : ℝ)*(sp8) + (2850612983711879/50000000000000 : ℝ)*(sp9) + (712668141898081/12500000000000 : ℝ)*(sp10) + (184637246002731/6250000000000 : ℝ)*(sp11) + (5090829329/50000000000000 : ℝ)*(sp12) + (184637246002731/6250000000000 : ℝ)*(f.failure) + (712668141898081/12500000000000 : ℝ)*(f.sum) + (294200646351/87250000000000000000000000 : ℝ)*base65 + (683773006736513/349000000000000000000000000000 : ℝ)*base67 + (475939955087487/349000000000000000000000000000 : ℝ)*base70 + (979147680939487/349000000000000000000000000000 : ℝ)*base72 + (371121750541/87250000000000000000000000 : ℝ)*base73 + (1102561316407487/349000000000000000000000000000 : ℝ)*base76 + (830222523089487/349000000000000000000000000000 : ℝ)*base78 + (10078433753487/349000000000000000000000000000 : ℝ)*base80 + (261709817083/87250000000000000000000000 : ℝ)*base81 + (140747/125000000000000000000 : ℝ)*base89 + (140747/125000000000000000000 : ℝ)*base91 + (140747/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-20707/25000 : ℝ) ≤ (-1806635752900842115880534314509/2181250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20331607/25000000000000 : ℝ)*(lower0) + (25063287/100000000000000 : ℝ)*(lower1) + (51742357/50000000000000 : ℝ)*(upper3) + (20076701/50000000000000 : ℝ)*(lower4) + (1093813099783467/25000000000000 : ℝ)*(major0) + (1093813099783467/25000000000000 : ℝ)*(major1) + (1093813099783467/25000000000000 : ℝ)*(major2) + (26459239/4000000000000 : ℝ)*(sp0) + (24888259661/100000000000000 : ℝ)*(sp6) + (121670627/20000000000000 : ℝ)*(sp8) + (2900304627140559/50000000000000 : ℝ)*(sp12) + (1450152631028807/25000000000000 : ℝ)*(sp13) + (362536602240973/6250000000000 : ℝ)*(sp14) + (74437571086057/2500000000000 : ℝ)*(sp15) + (74437571086057/2500000000000 : ℝ)*(f.failure) + (1450152631028807/25000000000000 : ℝ)*(f.sum) + (1769496153039/1745000000000000000000000000 : ℝ)*base66 + (16924538896626503/4362500000000000000000000000000 : ℝ)*base67 + (246837597154151503/4362500000000000000000000000000 : ℝ)*base69 + (12837551532764003/4362500000000000000000000000000 : ℝ)*base71 + (304424416973/54531250000000000000000000 : ℝ)*base73 + (182728683777564003/4362500000000000000000000000000 : ℝ)*base75 + (14690598072735997/4362500000000000000000000000000 : ℝ)*base78 + (47356096239285997/4362500000000000000000000000000 : ℝ)*base80 + (52051368210391/1745000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (459991/50000000000000000000 : ℝ)*base90 + (459991/50000000000000000000 : ℝ)*base92 + (459991/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1012_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59201/100000 : ℝ) else (79401/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20707/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1012_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59201/100000 : ℝ) else (79401/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20707/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
