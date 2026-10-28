-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1014_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:03:41.419388+00:00
-- url     : https://prove2.me/submissions/e11c9f1a-e41a-422b-9470-c5b114dd4f70

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
theorem support_rectangle_w1014_box_0 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049172289/5000000000 : ℝ)*x 0 + (5378060217/10000000000 : ℝ)*x 1 + (5378058923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049172289/5000000000 : ℝ)^8207 ≤ (1248493416981/10000000000000 : ℝ)^6159 := by
    have hnat : (1049172289 : ℕ)^8207*10000000000000^6159 ≤ 1248493416981^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049172289 5000000000 1248493416981 10000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378060217/10000000000 : ℝ)^8207 ≤ (8751507983861/20000000000000 : ℝ)^6159 := by
    have hnat : (5378060217 : ℕ)^8207*20000000000000^6159 ≤ 8751507983861^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378060217 10000000000 8751507983861 20000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378058923/10000000000 : ℝ)^8207 ≤ (21878762945007/50000000000000 : ℝ)^6159 := by
    have hnat : (5378058923 : ℕ)^8207*50000000000000^6159 ≤ 21878762945007^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378058923 10000000000 21878762945007 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049172289/5000000000 : ℝ), (5378060217/10000000000 : ℝ), (5378058923/10000000000 : ℝ)] ![(1248493416981/10000000000000 : ℝ), (8751507983861/20000000000000 : ℝ), (21878762945007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049172289/5000000000 : ℝ)|^8207 ≤ (1248493416981/10000000000000 : ℝ)^6159
        have hw : |(-1049172289/5000000000 : ℝ)|=(1049172289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378060217/10000000000 : ℝ)|^8207 ≤ (8751507983861/20000000000000 : ℝ)^6159
        have hw : |(5378060217/10000000000 : ℝ)|=(5378060217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378058923/10000000000 : ℝ)|^8207 ≤ (21878762945007/50000000000000 : ℝ)^6159
        have hw : |(5378058923/10000000000 : ℝ)|=(5378058923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_1 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330911081/625000000 : ℝ)*x 0 + (-1105604973/5000000000 : ℝ)*x 1 + (5378060273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330911081/625000000 : ℝ)^8207 ≤ (21427389343087/50000000000000 : ℝ)^6159 := by
    have hnat : (330911081 : ℕ)^8207*50000000000000^6159 ≤ 21427389343087^6159*625000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330911081 625000000 21427389343087 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105604973/5000000000 : ℝ)^8207 ≤ (6693840385889/50000000000000 : ℝ)^6159 := by
    have hnat : (1105604973 : ℕ)^8207*50000000000000^6159 ≤ 6693840385889^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105604973 5000000000 6693840385889 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378060273/10000000000 : ℝ)^8207 ≤ (21878770263223/50000000000000 : ℝ)^6159 := by
    have hnat : (5378060273 : ℕ)^8207*50000000000000^6159 ≤ 21878770263223^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378060273 10000000000 21878770263223 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330911081/625000000 : ℝ), (-1105604973/5000000000 : ℝ), (5378060273/10000000000 : ℝ)] ![(21427389343087/50000000000000 : ℝ), (6693840385889/50000000000000 : ℝ), (21878770263223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330911081/625000000 : ℝ)|^8207 ≤ (21427389343087/50000000000000 : ℝ)^6159
        have hw : |(330911081/625000000 : ℝ)|=(330911081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105604973/5000000000 : ℝ)|^8207 ≤ (6693840385889/50000000000000 : ℝ)^6159
        have hw : |(-1105604973/5000000000 : ℝ)|=(1105604973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378060273/10000000000 : ℝ)|^8207 ≤ (21878770263223/50000000000000 : ℝ)^6159
        have hw : |(5378060273/10000000000 : ℝ)|=(5378060273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_2 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132364431/250000000 : ℝ)*x 0 + (537806017/1000000000 : ℝ)*x 1 + (-2211210159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132364431/250000000 : ℝ)^8207 ≤ (42854778082183/100000000000000 : ℝ)^6159 := by
    have hnat : (132364431 : ℕ)^8207*100000000000000^6159 ≤ 42854778082183^6159*250000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132364431 250000000 42854778082183 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537806017/1000000000 : ℝ)^8207 ≤ (43757539409741/100000000000000 : ℝ)^6159 := by
    have hnat : (537806017 : ℕ)^8207*100000000000000^6159 ≤ 43757539409741^6159*1000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537806017 1000000000 43757539409741 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211210159/10000000000 : ℝ)^8207 ≤ (6693841245099/50000000000000 : ℝ)^6159 := by
    have hnat : (2211210159 : ℕ)^8207*50000000000000^6159 ≤ 6693841245099^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211210159 10000000000 6693841245099 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132364431/250000000 : ℝ), (537806017/1000000000 : ℝ), (-2211210159/10000000000 : ℝ)] ![(42854778082183/100000000000000 : ℝ), (43757539409741/100000000000000 : ℝ), (6693841245099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132364431/250000000 : ℝ)|^8207 ≤ (42854778082183/100000000000000 : ℝ)^6159
        have hw : |(132364431/250000000 : ℝ)|=(132364431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537806017/1000000000 : ℝ)|^8207 ≤ (43757539409741/100000000000000 : ℝ)^6159
        have hw : |(537806017/1000000000 : ℝ)|=(537806017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211210159/10000000000 : ℝ)|^8207 ≤ (6693841245099/50000000000000 : ℝ)^6159
        have hw : |(-2211210159/10000000000 : ℝ)|=(2211210159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_3 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (7018793/15625000 : ℝ)*x 0 + (4330725963/10000000000 : ℝ)*x 1 + (433072583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7018793/15625000 : ℝ)^8207 ≤ (688496960921/2000000000000 : ℝ)^6159 := by
    have hnat : (7018793 : ℕ)^8207*2000000000000^6159 ≤ 688496960921^6159*15625000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7018793 15625000 688496960921 2000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330725963/10000000000 : ℝ)^8207 ≤ (16393788320681/50000000000000 : ℝ)^6159 := by
    have hnat : (4330725963 : ℕ)^8207*50000000000000^6159 ≤ 16393788320681^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330725963 10000000000 16393788320681 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433072583/1000000000 : ℝ)^8207 ≤ (8196893824901/25000000000000 : ℝ)^6159 := by
    have hnat : (433072583 : ℕ)^8207*25000000000000^6159 ≤ 8196893824901^6159*1000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433072583 1000000000 8196893824901 25000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7018793/15625000 : ℝ), (4330725963/10000000000 : ℝ), (433072583/1000000000 : ℝ)] ![(688496960921/2000000000000 : ℝ), (16393788320681/50000000000000 : ℝ), (8196893824901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7018793/15625000 : ℝ)|^8207 ≤ (688496960921/2000000000000 : ℝ)^6159
        have hw : |(7018793/15625000 : ℝ)|=(7018793/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330725963/10000000000 : ℝ)|^8207 ≤ (16393788320681/50000000000000 : ℝ)^6159
        have hw : |(4330725963/10000000000 : ℝ)|=(4330725963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433072583/1000000000 : ℝ)|^8207 ≤ (8196893824901/25000000000000 : ℝ)^6159
        have hw : |(433072583/1000000000 : ℝ)|=(433072583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_4 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2362320027/10000000000 : ℝ)*x 0 + (2639635987/5000000000 : ℝ)*x 1 + (5279271839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2362320027/10000000000 : ℝ)^8207 ≤ (14620437836743/100000000000000 : ℝ)^6159 := by
    have hnat : (2362320027 : ℕ)^8207*100000000000000^6159 ≤ 14620437836743^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362320027 10000000000 14620437836743 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639635987/5000000000 : ℝ)^8207 ≤ (21344890899853/50000000000000 : ℝ)^6159 := by
    have hnat : (2639635987 : ℕ)^8207*50000000000000^6159 ≤ 21344890899853^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639635987 5000000000 21344890899853 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279271839/10000000000 : ℝ)^8207 ≤ (21344890172529/50000000000000 : ℝ)^6159 := by
    have hnat : (5279271839 : ℕ)^8207*50000000000000^6159 ≤ 21344890172529^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279271839 10000000000 21344890172529 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2362320027/10000000000 : ℝ), (2639635987/5000000000 : ℝ), (5279271839/10000000000 : ℝ)] ![(14620437836743/100000000000000 : ℝ), (21344890899853/50000000000000 : ℝ), (21344890172529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2362320027/10000000000 : ℝ)|^8207 ≤ (14620437836743/100000000000000 : ℝ)^6159
        have hw : |(-2362320027/10000000000 : ℝ)|=(2362320027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639635987/5000000000 : ℝ)|^8207 ≤ (21344890899853/50000000000000 : ℝ)^6159
        have hw : |(2639635987/5000000000 : ℝ)|=(2639635987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279271839/10000000000 : ℝ)|^8207 ≤ (21344890172529/50000000000000 : ℝ)^6159
        have hw : |(5279271839/10000000000 : ℝ)|=(5279271839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_5 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364575351/10000000000 : ℝ)*x 0 + (-2249664927/10000000000 : ℝ)*x 1 + (2639635987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364575351/10000000000 : ℝ)^8207 ≤ (43611400655861/100000000000000 : ℝ)^6159 := by
    have hnat : (5364575351 : ℕ)^8207*100000000000000^6159 ≤ 43611400655861^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364575351 10000000000 43611400655861 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249664927/10000000000 : ℝ)^8207 ≤ (1712352190009/12500000000000 : ℝ)^6159 := by
    have hnat : (2249664927 : ℕ)^8207*12500000000000^6159 ≤ 1712352190009^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249664927 10000000000 1712352190009 12500000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639635987/5000000000 : ℝ)^8207 ≤ (21344890899853/50000000000000 : ℝ)^6159 := by
    have hnat : (2639635987 : ℕ)^8207*50000000000000^6159 ≤ 21344890899853^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639635987 5000000000 21344890899853 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364575351/10000000000 : ℝ), (-2249664927/10000000000 : ℝ), (2639635987/5000000000 : ℝ)] ![(43611400655861/100000000000000 : ℝ), (1712352190009/12500000000000 : ℝ), (21344890899853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364575351/10000000000 : ℝ)|^8207 ≤ (43611400655861/100000000000000 : ℝ)^6159
        have hw : |(5364575351/10000000000 : ℝ)|=(5364575351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249664927/10000000000 : ℝ)|^8207 ≤ (1712352190009/12500000000000 : ℝ)^6159
        have hw : |(-2249664927/10000000000 : ℝ)|=(2249664927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639635987/5000000000 : ℝ)|^8207 ≤ (21344890899853/50000000000000 : ℝ)^6159
        have hw : |(2639635987/5000000000 : ℝ)|=(2639635987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_6 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682287803/5000000000 : ℝ)*x 0 + (2639635899/5000000000 : ℝ)*x 1 + (-2249664821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682287803/5000000000 : ℝ)^8207 ≤ (43611403418213/100000000000000 : ℝ)^6159 := by
    have hnat : (2682287803 : ℕ)^8207*100000000000000^6159 ≤ 43611403418213^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682287803 5000000000 43611403418213 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639635899/5000000000 : ℝ)^8207 ≤ (10672444975819/25000000000000 : ℝ)^6159 := by
    have hnat : (2639635899 : ℕ)^8207*25000000000000^6159 ≤ 10672444975819^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639635899 5000000000 10672444975819 25000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249664821/10000000000 : ℝ)^8207 ≤ (13698816659979/100000000000000 : ℝ)^6159 := by
    have hnat : (2249664821 : ℕ)^8207*100000000000000^6159 ≤ 13698816659979^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249664821 10000000000 13698816659979 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682287803/5000000000 : ℝ), (2639635899/5000000000 : ℝ), (-2249664821/10000000000 : ℝ)] ![(43611403418213/100000000000000 : ℝ), (10672444975819/25000000000000 : ℝ), (13698816659979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682287803/5000000000 : ℝ)|^8207 ≤ (43611403418213/100000000000000 : ℝ)^6159
        have hw : |(2682287803/5000000000 : ℝ)|=(2682287803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639635899/5000000000 : ℝ)|^8207 ≤ (10672444975819/25000000000000 : ℝ)^6159
        have hw : |(2639635899/5000000000 : ℝ)|=(2639635899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2249664821/10000000000 : ℝ)|^8207 ≤ (13698816659979/100000000000000 : ℝ)^6159
        have hw : |(-2249664821/10000000000 : ℝ)|=(2249664821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_7 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4273717819/10000000000 : ℝ)*x 0 + (887971759/2000000000 : ℝ)*x 1 + (2219929439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273717819/10000000000 : ℝ)^8207 ≤ (16106858684319/50000000000000 : ℝ)^6159 := by
    have hnat : (4273717819 : ℕ)^8207*50000000000000^6159 ≤ 16106858684319^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273717819 10000000000 16106858684319 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887971759/2000000000 : ℝ)^8207 ≤ (847328522153/2500000000000 : ℝ)^6159 := by
    have hnat : (887971759 : ℕ)^8207*2500000000000^6159 ≤ 847328522153^6159*2000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887971759 2000000000 847328522153 2500000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219929439/5000000000 : ℝ)^8207 ≤ (2118321358151/6250000000000 : ℝ)^6159 := by
    have hnat : (2219929439 : ℕ)^8207*6250000000000^6159 ≤ 2118321358151^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219929439 5000000000 2118321358151 6250000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273717819/10000000000 : ℝ), (887971759/2000000000 : ℝ), (2219929439/5000000000 : ℝ)] ![(16106858684319/50000000000000 : ℝ), (847328522153/2500000000000 : ℝ), (2118321358151/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273717819/10000000000 : ℝ)|^8207 ≤ (16106858684319/50000000000000 : ℝ)^6159
        have hw : |(4273717819/10000000000 : ℝ)|=(4273717819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(887971759/2000000000 : ℝ)|^8207 ≤ (847328522153/2500000000000 : ℝ)^6159
        have hw : |(887971759/2000000000 : ℝ)|=(887971759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219929439/5000000000 : ℝ)|^8207 ≤ (2118321358151/6250000000000 : ℝ)^6159
        have hw : |(2219929439/5000000000 : ℝ)|=(2219929439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_8 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2307280577/10000000000 : ℝ)*x 0 + (5212343221/10000000000 : ℝ)*x 1 + (2693826203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2307280577/10000000000 : ℝ)^8207 ≤ (7084147564631/50000000000000 : ℝ)^6159 := by
    have hnat : (2307280577 : ℕ)^8207*50000000000000^6159 ≤ 7084147564631^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307280577 10000000000 7084147564631 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212343221/10000000000 : ℝ)^8207 ≤ (41970137499219/100000000000000 : ℝ)^6159 := by
    have hnat : (5212343221 : ℕ)^8207*100000000000000^6159 ≤ 41970137499219^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212343221 10000000000 41970137499219 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693826203/5000000000 : ℝ)^8207 ≤ (43861567358749/100000000000000 : ℝ)^6159 := by
    have hnat : (2693826203 : ℕ)^8207*100000000000000^6159 ≤ 43861567358749^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693826203 5000000000 43861567358749 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2307280577/10000000000 : ℝ), (5212343221/10000000000 : ℝ), (2693826203/5000000000 : ℝ)] ![(7084147564631/50000000000000 : ℝ), (41970137499219/100000000000000 : ℝ), (43861567358749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2307280577/10000000000 : ℝ)|^8207 ≤ (7084147564631/50000000000000 : ℝ)^6159
        have hw : |(-2307280577/10000000000 : ℝ)|=(2307280577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212343221/10000000000 : ℝ)|^8207 ≤ (41970137499219/100000000000000 : ℝ)^6159
        have hw : |(5212343221/10000000000 : ℝ)|=(5212343221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693826203/5000000000 : ℝ)|^8207 ≤ (43861567358749/100000000000000 : ℝ)^6159
        have hw : |(2693826203/5000000000 : ℝ)|=(2693826203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_9 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287776101/10000000000 : ℝ)*x 0 + (-2207404893/10000000000 : ℝ)*x 1 + (538765253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287776101/10000000000 : ℝ)^8207 ≤ (21390719872937/50000000000000 : ℝ)^6159 := by
    have hnat : (5287776101 : ℕ)^8207*50000000000000^6159 ≤ 21390719872937^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287776101 10000000000 21390719872937 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207404893/10000000000 : ℝ)^8207 ≤ (13356991541861/100000000000000 : ℝ)^6159 := by
    have hnat : (2207404893 : ℕ)^8207*100000000000000^6159 ≤ 13356991541861^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207404893 10000000000 13356991541861 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538765253/1000000000 : ℝ)^8207 ≤ (4386156870393/10000000000000 : ℝ)^6159 := by
    have hnat : (538765253 : ℕ)^8207*10000000000000^6159 ≤ 4386156870393^6159*1000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538765253 1000000000 4386156870393 10000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287776101/10000000000 : ℝ), (-2207404893/10000000000 : ℝ), (538765253/1000000000 : ℝ)] ![(21390719872937/50000000000000 : ℝ), (13356991541861/100000000000000 : ℝ), (4386156870393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287776101/10000000000 : ℝ)|^8207 ≤ (21390719872937/50000000000000 : ℝ)^6159
        have hw : |(5287776101/10000000000 : ℝ)|=(5287776101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207404893/10000000000 : ℝ)|^8207 ≤ (13356991541861/100000000000000 : ℝ)^6159
        have hw : |(-2207404893/10000000000 : ℝ)|=(2207404893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538765253/1000000000 : ℝ)|^8207 ≤ (4386156870393/10000000000000 : ℝ)^6159
        have hw : |(538765253/1000000000 : ℝ)|=(538765253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_10 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660972073/1250000000 : ℝ)*x 0 + (5387652467/10000000000 : ℝ)*x 1 + (-220740433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660972073/1250000000 : ℝ)^8207 ≤ (42781444953067/100000000000000 : ℝ)^6159 := by
    have hnat : (660972073 : ℕ)^8207*100000000000000^6159 ≤ 42781444953067^6159*1250000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660972073 1250000000 42781444953067 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387652467/10000000000 : ℝ)^8207 ≤ (43861568020491/100000000000000 : ℝ)^6159 := by
    have hnat : (5387652467 : ℕ)^8207*100000000000000^6159 ≤ 43861568020491^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387652467 10000000000 43861568020491 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220740433/1000000000 : ℝ)^8207 ≤ (3339246750587/25000000000000 : ℝ)^6159 := by
    have hnat : (220740433 : ℕ)^8207*25000000000000^6159 ≤ 3339246750587^6159*1000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220740433 1000000000 3339246750587 25000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660972073/1250000000 : ℝ), (5387652467/10000000000 : ℝ), (-220740433/1000000000 : ℝ)] ![(42781444953067/100000000000000 : ℝ), (43861568020491/100000000000000 : ℝ), (3339246750587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660972073/1250000000 : ℝ)|^8207 ≤ (42781444953067/100000000000000 : ℝ)^6159
        have hw : |(660972073/1250000000 : ℝ)|=(660972073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387652467/10000000000 : ℝ)|^8207 ≤ (43861568020491/100000000000000 : ℝ)^6159
        have hw : |(5387652467/10000000000 : ℝ)|=(5387652467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220740433/1000000000 : ℝ)|^8207 ≤ (3339246750587/25000000000000 : ℝ)^6159
        have hw : |(-220740433/1000000000 : ℝ)|=(220740433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_11 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (902590589/2000000000 : ℝ)*x 0 + (2160061457/5000000000 : ℝ)*x 1 + (2160061211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902590589/2000000000 : ℝ)^8207 ≤ (34638700394427/100000000000000 : ℝ)^6159 := by
    have hnat : (902590589 : ℕ)^8207*100000000000000^6159 ≤ 34638700394427^6159*2000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902590589 2000000000 34638700394427 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160061457/5000000000 : ℝ)^8207 ≤ (6536130454471/20000000000000 : ℝ)^6159 := by
    have hnat : (2160061457 : ℕ)^8207*20000000000000^6159 ≤ 6536130454471^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160061457 5000000000 6536130454471 20000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160061211/5000000000 : ℝ)^8207 ≤ (326806473129/1000000000000 : ℝ)^6159 := by
    have hnat : (2160061211 : ℕ)^8207*1000000000000^6159 ≤ 326806473129^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160061211 5000000000 326806473129 1000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(902590589/2000000000 : ℝ), (2160061457/5000000000 : ℝ), (2160061211/5000000000 : ℝ)] ![(34638700394427/100000000000000 : ℝ), (6536130454471/20000000000000 : ℝ), (326806473129/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(902590589/2000000000 : ℝ)|^8207 ≤ (34638700394427/100000000000000 : ℝ)^6159
        have hw : |(902590589/2000000000 : ℝ)|=(902590589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2160061457/5000000000 : ℝ)|^8207 ≤ (6536130454471/20000000000000 : ℝ)^6159
        have hw : |(2160061457/5000000000 : ℝ)|=(2160061457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160061211/5000000000 : ℝ)|^8207 ≤ (326806473129/1000000000000 : ℝ)^6159
        have hw : |(2160061211/5000000000 : ℝ)|=(2160061211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_12 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269223451/1250000000 : ℝ)*x 0 + (5443611073/10000000000 : ℝ)*x 1 + (5271300349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269223451/1250000000 : ℝ)^8207 ≤ (6463213300109/50000000000000 : ℝ)^6159 := by
    have hnat : (269223451 : ℕ)^8207*50000000000000^6159 ≤ 6463213300109^6159*1250000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269223451 1250000000 6463213300109 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443611073/10000000000 : ℝ)^8207 ≤ (2223483281237/5000000000000 : ℝ)^6159 := by
    have hnat : (5443611073 : ℕ)^8207*5000000000000^6159 ≤ 2223483281237^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443611073 10000000000 2223483281237 5000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271300349/10000000000 : ℝ)^8207 ≤ (10650976939287/25000000000000 : ℝ)^6159 := by
    have hnat : (5271300349 : ℕ)^8207*25000000000000^6159 ≤ 10650976939287^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271300349 10000000000 10650976939287 25000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269223451/1250000000 : ℝ), (5443611073/10000000000 : ℝ), (5271300349/10000000000 : ℝ)] ![(6463213300109/50000000000000 : ℝ), (2223483281237/5000000000000 : ℝ), (10650976939287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269223451/1250000000 : ℝ)|^8207 ≤ (6463213300109/50000000000000 : ℝ)^6159
        have hw : |(-269223451/1250000000 : ℝ)|=(269223451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443611073/10000000000 : ℝ)|^8207 ≤ (2223483281237/5000000000000 : ℝ)^6159
        have hw : |(5443611073/10000000000 : ℝ)|=(5443611073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271300349/10000000000 : ℝ)|^8207 ≤ (10650976939287/25000000000000 : ℝ)^6159
        have hw : |(5271300349/10000000000 : ℝ)|=(5271300349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_13 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167819417/312500000 : ℝ)*x 0 + (-1126354299/5000000000 : ℝ)*x 1 + (2635650153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167819417/312500000 : ℝ)^8207 ≤ (21836286506787/50000000000000 : ℝ)^6159 := by
    have hnat : (167819417 : ℕ)^8207*50000000000000^6159 ≤ 21836286506787^6159*312500000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167819417 312500000 21836286506787 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126354299/5000000000 : ℝ)^8207 ≤ (6861759837157/50000000000000 : ℝ)^6159 := by
    have hnat : (1126354299 : ℕ)^8207*50000000000000^6159 ≤ 6861759837157^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126354299 5000000000 6861759837157 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635650153/5000000000 : ℝ)^8207 ≤ (1331372102939/3125000000000 : ℝ)^6159 := by
    have hnat : (2635650153 : ℕ)^8207*3125000000000^6159 ≤ 1331372102939^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635650153 5000000000 1331372102939 3125000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167819417/312500000 : ℝ), (-1126354299/5000000000 : ℝ), (2635650153/5000000000 : ℝ)] ![(21836286506787/50000000000000 : ℝ), (6861759837157/50000000000000 : ℝ), (1331372102939/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167819417/312500000 : ℝ)|^8207 ≤ (21836286506787/50000000000000 : ℝ)^6159
        have hw : |(167819417/312500000 : ℝ)|=(167819417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126354299/5000000000 : ℝ)|^8207 ≤ (6861759837157/50000000000000 : ℝ)^6159
        have hw : |(-1126354299/5000000000 : ℝ)|=(1126354299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635650153/5000000000 : ℝ)|^8207 ≤ (1331372102939/3125000000000 : ℝ)^6159
        have hw : |(2635650153/5000000000 : ℝ)|=(2635650153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_14 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370221339/10000000000 : ℝ)*x 0 + (5271300321/10000000000 : ℝ)*x 1 + (-1126354293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370221339/10000000000 : ℝ)^8207 ≤ (43672572959391/100000000000000 : ℝ)^6159 := by
    have hnat : (5370221339 : ℕ)^8207*100000000000000^6159 ≤ 43672572959391^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370221339 10000000000 43672572959391 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271300321/10000000000 : ℝ)^8207 ≤ (21301953727797/50000000000000 : ℝ)^6159 := by
    have hnat : (5271300321 : ℕ)^8207*50000000000000^6159 ≤ 21301953727797^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271300321 10000000000 21301953727797 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126354293/5000000000 : ℝ)^8207 ≤ (13723519576901/100000000000000 : ℝ)^6159 := by
    have hnat : (1126354293 : ℕ)^8207*100000000000000^6159 ≤ 13723519576901^6159*5000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126354293 5000000000 13723519576901 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370221339/10000000000 : ℝ), (5271300321/10000000000 : ℝ), (-1126354293/5000000000 : ℝ)] ![(43672572959391/100000000000000 : ℝ), (21301953727797/50000000000000 : ℝ), (13723519576901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370221339/10000000000 : ℝ)|^8207 ≤ (43672572959391/100000000000000 : ℝ)^6159
        have hw : |(5370221339/10000000000 : ℝ)|=(5370221339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271300321/10000000000 : ℝ)|^8207 ≤ (21301953727797/50000000000000 : ℝ)^6159
        have hw : |(5271300321/10000000000 : ℝ)|=(5271300321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126354293/5000000000 : ℝ)|^8207 ≤ (13723519576901/100000000000000 : ℝ)^6159
        have hw : |(-1126354293/5000000000 : ℝ)|=(1126354293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1014_box_15 (p : ℝ) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42558713/100000000 : ℝ)*x 0 + (4448660629/10000000000 : ℝ)*x 1 + (4448660619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42558713/100000000 : ℝ)^8207 ≤ (16017295228337/50000000000000 : ℝ)^6159 := by
    have hnat : (42558713 : ℕ)^8207*50000000000000^6159 ≤ 16017295228337^6159*100000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42558713 100000000 16017295228337 50000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4448660629/10000000000 : ℝ)^8207 ≤ (8495676202943/25000000000000 : ℝ)^6159 := by
    have hnat : (4448660629 : ℕ)^8207*25000000000000^6159 ≤ 8495676202943^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448660629 10000000000 8495676202943 25000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4448660619/10000000000 : ℝ)^8207 ≤ (33982704709983/100000000000000 : ℝ)^6159 := by
    have hnat : (4448660619 : ℕ)^8207*100000000000000^6159 ≤ 33982704709983^6159*10000000000^8207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448660619 10000000000 33982704709983 100000000000000 8207 6159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8207/2048 : ℝ)) 8207 6159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42558713/100000000 : ℝ), (4448660629/10000000000 : ℝ), (4448660619/10000000000 : ℝ)] ![(16017295228337/50000000000000 : ℝ), (8495676202943/25000000000000 : ℝ), (33982704709983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42558713/100000000 : ℝ)|^8207 ≤ (16017295228337/50000000000000 : ℝ)^6159
        have hw : |(42558713/100000000 : ℝ)|=(42558713/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4448660629/10000000000 : ℝ)|^8207 ≤ (8495676202943/25000000000000 : ℝ)^6159
        have hw : |(4448660629/10000000000 : ℝ)|=(4448660629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4448660619/10000000000 : ℝ)|^8207 ≤ (33982704709983/100000000000000 : ℝ)^6159
        have hw : |(4448660619/10000000000 : ℝ)|=(4448660619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1014_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146982509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29601/50000 : ℝ) ∧ (79407/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82833/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5589/50000 : ℝ) ^ (4103/1024 : ℝ) ≤ (15379814509341931/100000000000000000000 : ℝ) := by
    have hpowers : (5589/50000 : ℝ)^4103 ≤ (15379814509341931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5589 : ℕ)^4103*100000000000000000000^1024 ≤ 15379814509341931^1024*50000^4103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5589 50000 15379814509341931 100000000000000000000 4103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5589/50000 : ℝ)) (X := (15379814509341931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4103 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13969/100000 : ℝ) ^ (4103/1024 : ℝ) ≤ (37567965200316983/100000000000000000000 : ℝ) := by
    have hpowers : (13969/100000 : ℝ)^4103 ≤ (37567965200316983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13969 : ℕ)^4103*100000000000000000000^1024 ≤ 37567965200316983^1024*100000^4103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13969 100000 37567965200316983 100000000000000000000 4103 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13969/100000 : ℝ)) (X := (37567965200316983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4103 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015379814509341931/50000000000000000000 : ℝ) ≤ (10000767590189299/10000000000000000 : ℝ) ^ (4103/1024 : ℝ) := by
    have hpowers : (50015379814509341931/50000000000000000000 : ℝ)^1024 ≤ (10000767590189299/10000000000000000 : ℝ)^4103 := by
      have hnat : (50015379814509341931 : ℕ)^1024*10000000000000000^4103 ≤ 10000767590189299^4103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015379814509341931 50000000000000000000 10000767590189299 10000000000000000 1024 4103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000767590189299/10000000000000000 : ℝ)) (X := (50015379814509341931/50000000000000000000 : ℝ)) (by norm_num) 4103 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026473889854829457/50000000000000000000 : ℝ) ≤ (5000660586867077/5000000000000000 : ℝ) ^ (4103/1024 : ℝ) := by
    have hpowers : (50026473889854829457/50000000000000000000 : ℝ)^1024 ≤ (5000660586867077/5000000000000000 : ℝ)^4103 := by
      have hnat : (50026473889854829457 : ℕ)^1024*5000000000000000^4103 ≤ 5000660586867077^4103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026473889854829457 50000000000000000000 5000660586867077 5000000000000000 1024 4103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660586867077/5000000000000000 : ℝ)) (X := (50026473889854829457/50000000000000000000 : ℝ)) (by norm_num) 4103 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037567965200316983/50000000000000000000 : ℝ) ≤ (10001874757279009/10000000000000000 : ℝ) ^ (4103/1024 : ℝ) := by
    have hpowers : (50037567965200316983/50000000000000000000 : ℝ)^1024 ≤ (10001874757279009/10000000000000000 : ℝ)^4103 := by
      have hnat : (50037567965200316983 : ℕ)^1024*10000000000000000^4103 ≤ 10001874757279009^4103*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037567965200316983 50000000000000000000 10001874757279009 10000000000000000 1024 4103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001874757279009/10000000000000000 : ℝ)) (X := (50037567965200316983/50000000000000000000 : ℝ)) (by norm_num) 4103 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15379814509341931/100000000000000000000 : ℝ) ≤ ((27899766430489555129/27910000000000000000 : ℝ)+2*(110716708971/55820000000000 : ℝ)*(5589/50000 : ℝ))^(4103/1024 : ℝ) := by
    rw [show (27899766430489555129/27910000000000000000 : ℝ)+2*(110716708971/55820000000000 : ℝ)*(5589/50000 : ℝ)=(10000767590189299/10000000000000000 : ℝ) by norm_num, show 1+2*(15379814509341931/100000000000000000000 : ℝ)=(50015379814509341931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37567965200316983/100000000000000000000 : ℝ)+(15379814509341931/100000000000000000000 : ℝ) ≤ ((27899766430489555129/27910000000000000000 : ℝ)+(110716708971/55820000000000 : ℝ)*((13969/100000 : ℝ)+(5589/50000 : ℝ)))^(4103/1024 : ℝ) := by
    rw [show (27899766430489555129/27910000000000000000 : ℝ)+(110716708971/55820000000000 : ℝ)*((13969/100000 : ℝ)+(5589/50000 : ℝ))=(5000660586867077/5000000000000000 : ℝ) by norm_num, show 1+(37567965200316983/100000000000000000000 : ℝ)+(15379814509341931/100000000000000000000 : ℝ)=(50026473889854829457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37567965200316983/100000000000000000000 : ℝ) ≤ ((27899766430489555129/27910000000000000000 : ℝ)+2*(110716708971/55820000000000 : ℝ)*(13969/100000 : ℝ))^(4103/1024 : ℝ) := by
    rw [show (27899766430489555129/27910000000000000000 : ℝ)+2*(110716708971/55820000000000 : ℝ)*(13969/100000 : ℝ)=(10001874757279009/10000000000000000 : ℝ) by norm_num, show 1+2*(37567965200316983/100000000000000000000 : ℝ)=(50037567965200316983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27899766430489555129/27910000000000000000 : ℝ)*(X 1 0+X 2 0)+(110716708971/55820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4103/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (13969/100000 : ℝ)) (c := (27899766430489555129/27910000000000000000 : ℝ)) (alpha := (110716708971/55820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27899766430489555129/27910000000000000000 : ℝ)*(X 0 1+X 2 1)+(110716708971/55820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4103/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (13969/100000 : ℝ)) (c := (27899766430489555129/27910000000000000000 : ℝ)) (alpha := (110716708971/55820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27899766430489555129/27910000000000000000 : ℝ)*(X 0 2+X 1 2)+(110716708971/55820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4103/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (13969/100000 : ℝ)) (c := (27899766430489555129/27910000000000000000 : ℝ)) (alpha := (110716708971/55820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049172289/5000000000 : ℝ)*X 0 0+(5378060217/10000000000 : ℝ)*X 0 1+(5378058923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330911081/625000000 : ℝ)*X 1 0+(-1105604973/5000000000 : ℝ)*X 1 1+(5378060273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132364431/250000000 : ℝ)*X 2 0+(537806017/1000000000 : ℝ)*X 2 1+(-2211210159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((7018793/15625000 : ℝ)*X 0 0+(4330725963/10000000000 : ℝ)*X 0 1+(433072583/1000000000 : ℝ)*X 0 2+(7018793/15625000 : ℝ)*X 1 0+(4330725963/10000000000 : ℝ)*X 1 1+(433072583/1000000000 : ℝ)*X 1 2+(7018793/15625000 : ℝ)*X 2 0+(4330725963/10000000000 : ℝ)*X 2 1+(433072583/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2362320027/10000000000 : ℝ)*X 0 0+(2639635987/5000000000 : ℝ)*X 0 1+(5279271839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364575351/10000000000 : ℝ)*X 1 0+(-2249664927/10000000000 : ℝ)*X 1 1+(2639635987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682287803/5000000000 : ℝ)*X 2 0+(2639635899/5000000000 : ℝ)*X 2 1+(-2249664821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273717819/10000000000 : ℝ)*X 0 0+(887971759/2000000000 : ℝ)*X 0 1+(2219929439/5000000000 : ℝ)*X 0 2+(4273717819/10000000000 : ℝ)*X 1 0+(887971759/2000000000 : ℝ)*X 1 1+(2219929439/5000000000 : ℝ)*X 1 2+(4273717819/10000000000 : ℝ)*X 2 0+(887971759/2000000000 : ℝ)*X 2 1+(2219929439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2307280577/10000000000 : ℝ)*X 0 0+(5212343221/10000000000 : ℝ)*X 0 1+(2693826203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287776101/10000000000 : ℝ)*X 1 0+(-2207404893/10000000000 : ℝ)*X 1 1+(538765253/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((660972073/1250000000 : ℝ)*X 2 0+(5387652467/10000000000 : ℝ)*X 2 1+(-220740433/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((902590589/2000000000 : ℝ)*X 0 0+(2160061457/5000000000 : ℝ)*X 0 1+(2160061211/5000000000 : ℝ)*X 0 2+(902590589/2000000000 : ℝ)*X 1 0+(2160061457/5000000000 : ℝ)*X 1 1+(2160061211/5000000000 : ℝ)*X 1 2+(902590589/2000000000 : ℝ)*X 2 0+(2160061457/5000000000 : ℝ)*X 2 1+(2160061211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-269223451/1250000000 : ℝ)*X 0 0+(5443611073/10000000000 : ℝ)*X 0 1+(5271300349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((167819417/312500000 : ℝ)*X 1 0+(-1126354299/5000000000 : ℝ)*X 1 1+(2635650153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370221339/10000000000 : ℝ)*X 2 0+(5271300321/10000000000 : ℝ)*X 2 1+(-1126354293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((42558713/100000000 : ℝ)*X 0 0+(4448660629/10000000000 : ℝ)*X 0 1+(4448660619/10000000000 : ℝ)*X 0 2+(42558713/100000000 : ℝ)*X 1 0+(4448660629/10000000000 : ℝ)*X 1 1+(4448660619/10000000000 : ℝ)*X 1 2+(42558713/100000000 : ℝ)*X 2 0+(4448660629/10000000000 : ℝ)*X 2 1+(4448660619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1014_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-868286099200068391700268278942301/1395500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30846283/50000000000000 : ℝ)*(upper0) + (52606501/50000000000000 : ℝ)*(lower2) + (26248461/100000000000000 : ℝ)*(upper5) + (476530521783199/12500000000000 : ℝ)*(major0) + (476530521783199/12500000000000 : ℝ)*(major1) + (3812244174265593/100000000000000 : ℝ)*(major2) + (199776497/10000000000000 : ℝ)*(sp2) + (49026979/4000000000000 : ℝ)*(sp3) + (2525775728476691/50000000000000 : ℝ)*(sp4) + (1262884865452057/25000000000000 : ℝ)*(sp5) + (252577724926567/5000000000000 : ℝ)*(sp6) + (518734153971817/20000000000000 : ℝ)*(sp7) + (314958933/6250000000000 : ℝ)*(sp8) + (8517244041/50000000000000 : ℝ)*(sp13) + (1296835997766779/50000000000000 : ℝ)*(f.failure) + (505155649629631/10000000000000 : ℝ)*(f.sum) + (223915914369/1116400000000000000000000000 : ℝ)*base65 + (8359845210202834829/348875000000000000000000000000000 : ℝ)*base68 + (2839510103708623503/2791000000000000000000000000000000 : ℝ)*base70 + (6323424748045959829/348875000000000000000000000000000 : ℝ)*base72 + (102207994969221/5582000000000000000000000000 : ℝ)*base74 + (1768494270026623503/2791000000000000000000000000000000 : ℝ)*base76 + (7214381443577147329/348875000000000000000000000000000 : ℝ)*base78 + (6199269891466522329/348875000000000000000000000000000 : ℝ)*base80 + (2613692861289/1395500000000000000000000000 : ℝ)*base82 + (25731489/5000000000000000000000 : ℝ)*base90 + (25731489/5000000000000000000000 : ℝ)*base92 + (75731489/5000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29601/50000 : ℝ) ≤ (12909454648309885468592279182179/21804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (87198563/100000000000000 : ℝ)*(lower1) + (574659/800000000000 : ℝ)*(upper3) + (174571437/100000000000000 : ℝ)*(lower5) + (121073585735067/3125000000000 : ℝ)*(major0) + (121073585735067/3125000000000 : ℝ)*(major1) + (121073585735067/3125000000000 : ℝ)*(major2) + (203720861600503/4000000000000 : ℝ)*(sp0) + (203719768269061/4000000000000 : ℝ)*(sp1) + (2037196052969/40000000000 : ℝ)*(sp2) + (41186075386139/1562500000000 : ℝ)*(sp3) + (51185015853/100000000000000 : ℝ)*(sp5) + (55259319879/100000000000000 : ℝ)*(sp6) + (10143386081/50000000000000 : ℝ)*(sp7) + (5962932451/25000000000000 : ℝ)*(sp8) + (2635929111485057/100000000000000 : ℝ)*(f.failure) + (2546522695871189/50000000000000 : ℝ)*(f.sum) + (2861193523029/697750000000000000000000000 : ℝ)*base66 + (891385171552960107/87218750000000000000000000000000 : ℝ)*base68 + (1983819998988039893/87218750000000000000000000000000 : ℝ)*base69 + (78602127036210107/87218750000000000000000000000000 : ℝ)*base72 + (21187348261463/2791000000000000000000000000 : ℝ)*base74 + (4877938975212522607/87218750000000000000000000000000 : ℝ)*base76 + (628442721909991357/87218750000000000000000000000000 : ℝ)*base78 + (929500636007741357/87218750000000000000000000000000 : ℝ)*base80 + (53393961668037/2791000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6131987/10000000000000000000000 : ℝ)*base90 + (6131987/10000000000000000000000 : ℝ)*base92 + (6131987/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79407/100000 : ℝ) ≤ (554078767208937185971590708521157/697750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20086593/100000000000000 : ℝ)*(upper0) + (38942461/50000000000000 : ℝ)*(lower3) + (16581843/4000000000000 : ℝ)*(upper4) + (2171298364178763/50000000000000 : ℝ)*(major0) + (2171298364178763/50000000000000 : ℝ)*(major1) + (2171298364178763/50000000000000 : ℝ)*(major2) + (80154992849/50000000000000 : ℝ)*(sp1) + (364761825343/100000000000000 : ℝ)*(sp2) + (11601143269/5000000000000 : ℝ)*(sp3) + (59468119/12500000000000 : ℝ)*(sp4) + (5704224216880887/100000000000000 : ℝ)*(sp8) + (5704064382640141/100000000000000 : ℝ)*(sp9) + (356491245675031/6250000000000 : ℝ)*(sp10) + (369283369571591/12500000000000 : ℝ)*(sp11) + (738624744859527/25000000000000 : ℝ)*(f.failure) + (5704224692625839/100000000000000 : ℝ)*(f.sum) + (936073989341/2791000000000000000000000000 : ℝ)*base66 + (10150007446667525427/1395500000000000000000000000000000 : ℝ)*base67 + (27366987497933025427/1395500000000000000000000000000000 : ℝ)*base69 + (8461198741976525427/1395500000000000000000000000000000 : ℝ)*base71 + (8897472309589/558200000000000000000000000 : ℝ)*base73 + (17529812941786025427/1395500000000000000000000000000000 : ℝ)*base75 + (9230403735584025427/1395500000000000000000000000000000 : ℝ)*base77 + (54443708201369025427/1395500000000000000000000000000000 : ℝ)*base79 + (18530287637137/2791000000000000000000000000 : ℝ)*base81 + (18986757/2500000000000000000000 : ℝ)*base90 + (18986757/2500000000000000000000 : ℝ)*base92 + (18986757/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82833/100000 : ℝ) ≤ (-577949146862167854734431986748017/697750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10437699/100000000000000 : ℝ)*(lower0) + (3855399/100000000000000 : ℝ)*(lower1) + (1477917/100000000000000 : ℝ)*(lower2) + (2052027/25000000000000 : ℝ)*(lower3) + (2188410514860509/50000000000000 : ℝ)*(major0) + (2188410514860509/50000000000000 : ℝ)*(major1) + (2188410514860509/50000000000000 : ℝ)*(major2) + (25844286141/100000000000000 : ℝ)*(sp5) + (18088022847/100000000000000 : ℝ)*(sp6) + (10820829/1000000000000 : ℝ)*(sp7) + (1450867151649451/25000000000000 : ℝ)*(sp12) + (5803442762311663/100000000000000 : ℝ)*(sp13) + (5803450518574957/100000000000000 : ℝ)*(sp14) + (744445626392257/25000000000000 : ℝ)*(sp15) + (372222948456491/12500000000000 : ℝ)*(f.failure) + (1450867151649451/25000000000000 : ℝ)*(f.sum) + (1474434429009/279100000000000000000000000 : ℝ)*base65 + (8293893145538000661/1395500000000000000000000000000000 : ℝ)*base67 + (1792976676603999339/1395500000000000000000000000000000 : ℝ)*base70 + (525037845396499339/1395500000000000000000000000000000 : ℝ)*base72 + (12411444513943/2791000000000000000000000000 : ℝ)*base74 + (13974781274731999339/1395500000000000000000000000000000 : ℝ)*base76 + (2102643800442500661/1395500000000000000000000000000000 : ℝ)*base77 + (3332779871012499339/1395500000000000000000000000000000 : ℝ)*base80 + (501736985433/558200000000000000000000000 : ℝ)*base81 + (484081/1250000000000000000000 : ℝ)*base90 + (484081/1250000000000000000000 : ℝ)*base92 + (484081/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1014_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146982509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29601/50000 : ℝ) else (79407/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82833/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1014_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4103/1024 : ℝ) ≤ p) (hpb : p ≤ (8207/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (146982509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29601/50000 : ℝ) else (79407/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82833/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1014_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
