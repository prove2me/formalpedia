-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:07:49.883019+00:00
-- url     : https://prove2.me/submissions/19ffd441-543f-4daf-a2a9-1fef397f7328

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
theorem support_rectangle_w1018_box_0 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096474681/10000000000 : ℝ)*x 0 + (336125569/625000000 : ℝ)*x 1 + (1344502187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096474681/10000000000 : ℝ)^8211 ≤ (2494863300099/20000000000000 : ℝ)^6163 := by
    have hnat : (2096474681 : ℕ)^8211*20000000000000^6163 ≤ 2494863300099^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096474681 10000000000 2494863300099 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336125569/625000000 : ℝ)^8211 ≤ (10940710917983/25000000000000 : ℝ)^6163 := by
    have hnat : (336125569 : ℕ)^8211*25000000000000^6163 ≤ 10940710917983^6163*625000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336125569 625000000 10940710917983 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344502187/2500000000 : ℝ)^8211 ≤ (43762839812371/100000000000000 : ℝ)^6163 := by
    have hnat : (1344502187 : ℕ)^8211*100000000000000^6163 ≤ 43762839812371^6163*2500000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344502187 2500000000 43762839812371 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096474681/10000000000 : ℝ), (336125569/625000000 : ℝ), (1344502187/2500000000 : ℝ)] ![(2494863300099/20000000000000 : ℝ), (10940710917983/25000000000000 : ℝ), (43762839812371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096474681/10000000000 : ℝ)|^8211 ≤ (2494863300099/20000000000000 : ℝ)^6163
        have hw : |(-2096474681/10000000000 : ℝ)|=(2096474681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336125569/625000000 : ℝ)|^8211 ≤ (10940710917983/25000000000000 : ℝ)^6163
        have hw : |(336125569/625000000 : ℝ)|=(336125569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344502187/2500000000 : ℝ)|^8211 ≤ (43762839812371/100000000000000 : ℝ)^6163
        have hw : |(1344502187/2500000000 : ℝ)|=(1344502187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_1 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330914287/625000000 : ℝ)*x 0 + (-2209214651/10000000000 : ℝ)*x 1 + (2689004493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330914287/625000000 : ℝ)^8211 ≤ (8572242736371/20000000000000 : ℝ)^6163 := by
    have hnat : (330914287 : ℕ)^8211*20000000000000^6163 ≤ 8572242736371^6163*625000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330914287 625000000 8572242736371 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209214651/10000000000 : ℝ)^8211 ≤ (1671992988977/12500000000000 : ℝ)^6163 := by
    have hnat : (2209214651 : ℕ)^8211*12500000000000^6163 ≤ 1671992988977^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209214651 10000000000 1671992988977 12500000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2689004493/5000000000 : ℝ)^8211 ≤ (43762842392639/100000000000000 : ℝ)^6163 := by
    have hnat : (2689004493 : ℕ)^8211*100000000000000^6163 ≤ 43762842392639^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689004493 5000000000 43762842392639 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330914287/625000000 : ℝ), (-2209214651/10000000000 : ℝ), (2689004493/5000000000 : ℝ)] ![(8572242736371/20000000000000 : ℝ), (1671992988977/12500000000000 : ℝ), (43762842392639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330914287/625000000 : ℝ)|^8211 ≤ (8572242736371/20000000000000 : ℝ)^6163
        have hw : |(330914287/625000000 : ℝ)|=(330914287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209214651/10000000000 : ℝ)|^8211 ≤ (1671992988977/12500000000000 : ℝ)^6163
        have hw : |(-2209214651/10000000000 : ℝ)|=(2209214651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2689004493/5000000000 : ℝ)|^8211 ≤ (43762842392639/100000000000000 : ℝ)^6163
        have hw : |(2689004493/5000000000 : ℝ)|=(2689004493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_2 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294628679/10000000000 : ℝ)*x 0 + (2689004439/5000000000 : ℝ)*x 1 + (-2209214679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294628679/10000000000 : ℝ)^8211 ≤ (42861214620177/100000000000000 : ℝ)^6163 := by
    have hnat : (5294628679 : ℕ)^8211*100000000000000^6163 ≤ 42861214620177^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294628679 10000000000 42861214620177 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2689004439/5000000000 : ℝ)^8211 ≤ (43762841221761/100000000000000 : ℝ)^6163 := by
    have hnat : (2689004439 : ℕ)^8211*100000000000000^6163 ≤ 43762841221761^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689004439 5000000000 43762841221761 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209214679/10000000000 : ℝ)^8211 ≤ (13375944137681/100000000000000 : ℝ)^6163 := by
    have hnat : (2209214679 : ℕ)^8211*100000000000000^6163 ≤ 13375944137681^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209214679 10000000000 13375944137681 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294628679/10000000000 : ℝ), (2689004439/5000000000 : ℝ), (-2209214679/10000000000 : ℝ)] ![(42861214620177/100000000000000 : ℝ), (43762841221761/100000000000000 : ℝ), (13375944137681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294628679/10000000000 : ℝ)|^8211 ≤ (42861214620177/100000000000000 : ℝ)^6163
        have hw : |(5294628679/10000000000 : ℝ)|=(5294628679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2689004439/5000000000 : ℝ)|^8211 ≤ (43762841221761/100000000000000 : ℝ)^6163
        have hw : |(2689004439/5000000000 : ℝ)|=(2689004439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209214679/10000000000 : ℝ)|^8211 ≤ (13375944137681/100000000000000 : ℝ)^6163
        have hw : |(-2209214679/10000000000 : ℝ)|=(2209214679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_3 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4491397131/10000000000 : ℝ)*x 0 + (4330163343/10000000000 : ℝ)*x 1 + (433016307/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491397131/10000000000 : ℝ)^8211 ≤ (17212178449249/50000000000000 : ℝ)^6163 := by
    have hnat : (4491397131 : ℕ)^8211*50000000000000^6163 ≤ 17212178449249^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491397131 10000000000 17212178449249 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330163343/10000000000 : ℝ)^8211 ≤ (32787822923657/100000000000000 : ℝ)^6163 := by
    have hnat : (4330163343 : ℕ)^8211*100000000000000^6163 ≤ 32787822923657^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330163343 10000000000 32787822923657 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433016307/1000000000 : ℝ)^8211 ≤ (8196955042397/25000000000000 : ℝ)^6163 := by
    have hnat : (433016307 : ℕ)^8211*25000000000000^6163 ≤ 8196955042397^6163*1000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433016307 1000000000 8196955042397 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491397131/10000000000 : ℝ), (4330163343/10000000000 : ℝ), (433016307/1000000000 : ℝ)] ![(17212178449249/50000000000000 : ℝ), (32787822923657/100000000000000 : ℝ), (8196955042397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491397131/10000000000 : ℝ)|^8211 ≤ (17212178449249/50000000000000 : ℝ)^6163
        have hw : |(4491397131/10000000000 : ℝ)|=(4491397131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330163343/10000000000 : ℝ)|^8211 ≤ (32787822923657/100000000000000 : ℝ)^6163
        have hw : |(4330163343/10000000000 : ℝ)|=(4330163343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433016307/1000000000 : ℝ)|^8211 ≤ (8196955042397/25000000000000 : ℝ)^6163
        have hw : |(433016307/1000000000 : ℝ)|=(433016307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_4 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2360168137/10000000000 : ℝ)*x 0 + (42234703/80000000 : ℝ)*x 1 + (105586757/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2360168137/10000000000 : ℝ)^8211 ≤ (3651811234087/25000000000000 : ℝ)^6163 := by
    have hnat : (2360168137 : ℕ)^8211*25000000000000^6163 ≤ 3651811234087^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360168137 10000000000 3651811234087 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42234703/80000000 : ℝ)^8211 ≤ (2668523603837/6250000000000 : ℝ)^6163 := by
    have hnat : (42234703 : ℕ)^8211*6250000000000^6163 ≤ 2668523603837^6163*80000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42234703 80000000 2668523603837 6250000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105586757/200000000 : ℝ)^8211 ≤ (21348188696009/50000000000000 : ℝ)^6163 := by
    have hnat : (105586757 : ℕ)^8211*50000000000000^6163 ≤ 21348188696009^6163*200000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105586757 200000000 21348188696009 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2360168137/10000000000 : ℝ), (42234703/80000000 : ℝ), (105586757/200000000 : ℝ)] ![(3651811234087/25000000000000 : ℝ), (2668523603837/6250000000000 : ℝ), (21348188696009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2360168137/10000000000 : ℝ)|^8211 ≤ (3651811234087/25000000000000 : ℝ)^6163
        have hw : |(-2360168137/10000000000 : ℝ)|=(2360168137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42234703/80000000 : ℝ)|^8211 ≤ (2668523603837/6250000000000 : ℝ)^6163
        have hw : |(42234703/80000000 : ℝ)|=(42234703/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105586757/200000000 : ℝ)|^8211 ≤ (21348188696009/50000000000000 : ℝ)^6163
        have hw : |(105586757/200000000 : ℝ)|=(105586757/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_5 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072907483/2000000000 : ℝ)*x 0 + (-561909197/2500000000 : ℝ)*x 1 + (1319834437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072907483/2000000000 : ℝ)^8211 ≤ (43616851678197/100000000000000 : ℝ)^6163 := by
    have hnat : (1072907483 : ℕ)^8211*100000000000000^6163 ≤ 43616851678197^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072907483 2000000000 43616851678197 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561909197/2500000000 : ℝ)^8211 ≤ (13686772018449/100000000000000 : ℝ)^6163 := by
    have hnat : (561909197 : ℕ)^8211*100000000000000^6163 ≤ 13686772018449^6163*2500000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561909197 2500000000 13686772018449 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319834437/2500000000 : ℝ)^8211 ≤ (42696376292973/100000000000000 : ℝ)^6163 := by
    have hnat : (1319834437 : ℕ)^8211*100000000000000^6163 ≤ 42696376292973^6163*2500000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319834437 2500000000 42696376292973 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072907483/2000000000 : ℝ), (-561909197/2500000000 : ℝ), (1319834437/2500000000 : ℝ)] ![(43616851678197/100000000000000 : ℝ), (13686772018449/100000000000000 : ℝ), (42696376292973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072907483/2000000000 : ℝ)|^8211 ≤ (43616851678197/100000000000000 : ℝ)^6163
        have hw : |(1072907483/2000000000 : ℝ)|=(1072907483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561909197/2500000000 : ℝ)|^8211 ≤ (13686772018449/100000000000000 : ℝ)^6163
        have hw : |(-561909197/2500000000 : ℝ)|=(561909197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1319834437/2500000000 : ℝ)|^8211 ≤ (42696376292973/100000000000000 : ℝ)^6163
        have hw : |(1319834437/2500000000 : ℝ)|=(1319834437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_6 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364537097/10000000000 : ℝ)*x 0 + (2639669001/5000000000 : ℝ)*x 1 + (-3596219/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364537097/10000000000 : ℝ)^8211 ≤ (10904212058371/25000000000000 : ℝ)^6163 := by
    have hnat : (5364537097 : ℕ)^8211*25000000000000^6163 ≤ 10904212058371^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364537097 10000000000 10904212058371 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639669001/5000000000 : ℝ)^8211 ≤ (42696379029811/100000000000000 : ℝ)^6163 := by
    have hnat : (2639669001 : ℕ)^8211*100000000000000^6163 ≤ 42696379029811^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639669001 5000000000 42696379029811 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3596219/16000000 : ℝ)^8211 ≤ (547470908971/4000000000000 : ℝ)^6163 := by
    have hnat : (3596219 : ℕ)^8211*4000000000000^6163 ≤ 547470908971^6163*16000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3596219 16000000 547470908971 4000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364537097/10000000000 : ℝ), (2639669001/5000000000 : ℝ), (-3596219/16000000 : ℝ)] ![(10904212058371/25000000000000 : ℝ), (42696379029811/100000000000000 : ℝ), (547470908971/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364537097/10000000000 : ℝ)|^8211 ≤ (10904212058371/25000000000000 : ℝ)^6163
        have hw : |(5364537097/10000000000 : ℝ)|=(5364537097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639669001/5000000000 : ℝ)|^8211 ≤ (42696379029811/100000000000000 : ℝ)^6163
        have hw : |(2639669001/5000000000 : ℝ)|=(2639669001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3596219/16000000 : ℝ)|^8211 ≤ (547470908971/4000000000000 : ℝ)^6163
        have hw : |(-3596219/16000000 : ℝ)|=(3596219/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_7 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2136589687/5000000000 : ℝ)*x 0 + (4439250089/10000000000 : ℝ)*x 1 + (4439250323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136589687/5000000000 : ℝ)^8211 ≤ (8053554972623/25000000000000 : ℝ)^6163 := by
    have hnat : (2136589687 : ℕ)^8211*25000000000000^6163 ≤ 8053554972623^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136589687 5000000000 8053554972623 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4439250089/10000000000 : ℝ)^8211 ≤ (847322221483/2500000000000 : ℝ)^6163 := by
    have hnat : (4439250089 : ℕ)^8211*2500000000000^6163 ≤ 847322221483^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439250089 10000000000 847322221483 2500000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439250323/10000000000 : ℝ)^8211 ≤ (33892891239549/100000000000000 : ℝ)^6163 := by
    have hnat : (4439250323 : ℕ)^8211*100000000000000^6163 ≤ 33892891239549^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439250323 10000000000 33892891239549 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136589687/5000000000 : ℝ), (4439250089/10000000000 : ℝ), (4439250323/10000000000 : ℝ)] ![(8053554972623/25000000000000 : ℝ), (847322221483/2500000000000 : ℝ), (33892891239549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136589687/5000000000 : ℝ)|^8211 ≤ (8053554972623/25000000000000 : ℝ)^6163
        have hw : |(2136589687/5000000000 : ℝ)|=(2136589687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4439250089/10000000000 : ℝ)|^8211 ≤ (847322221483/2500000000000 : ℝ)^6163
        have hw : |(4439250089/10000000000 : ℝ)|=(4439250089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439250323/10000000000 : ℝ)|^8211 ≤ (33892891239549/100000000000000 : ℝ)^6163
        have hw : |(4439250323/10000000000 : ℝ)|=(4439250323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_8 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-288147797/1250000000 : ℝ)*x 0 + (5212480149/10000000000 : ℝ)*x 1 + (5387602403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288147797/1250000000 : ℝ)^8211 ≤ (3538902827101/25000000000000 : ℝ)^6163 := by
    have hnat : (288147797 : ℕ)^8211*25000000000000^6163 ≤ 3538902827101^6163*1250000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288147797 1250000000 3538902827101 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212480149/10000000000 : ℝ)^8211 ≤ (20988754398367/50000000000000 : ℝ)^6163 := by
    have hnat : (5212480149 : ℕ)^8211*50000000000000^6163 ≤ 20988754398367^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212480149 10000000000 20988754398367 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387602403/10000000000 : ℝ)^8211 ≤ (43866879879843/100000000000000 : ℝ)^6163 := by
    have hnat : (5387602403 : ℕ)^8211*100000000000000^6163 ≤ 43866879879843^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387602403 10000000000 43866879879843 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-288147797/1250000000 : ℝ), (5212480149/10000000000 : ℝ), (5387602403/10000000000 : ℝ)] ![(3538902827101/25000000000000 : ℝ), (20988754398367/50000000000000 : ℝ), (43866879879843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-288147797/1250000000 : ℝ)|^8211 ≤ (3538902827101/25000000000000 : ℝ)^6163
        have hw : |(-288147797/1250000000 : ℝ)|=(288147797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212480149/10000000000 : ℝ)|^8211 ≤ (20988754398367/50000000000000 : ℝ)^6163
        have hw : |(5212480149/10000000000 : ℝ)|=(5212480149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387602403/10000000000 : ℝ)|^8211 ≤ (43866879879843/100000000000000 : ℝ)^6163
        have hw : |(5387602403/10000000000 : ℝ)|=(5387602403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_9 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057565503/2000000000 : ℝ)*x 0 + (-441081519/2000000000 : ℝ)*x 1 + (1077520477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057565503/2000000000 : ℝ)^8211 ≤ (10696969395337/25000000000000 : ℝ)^6163 := by
    have hnat : (1057565503 : ℕ)^8211*25000000000000^6163 ≤ 10696969395337^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057565503 2000000000 10696969395337 25000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441081519/2000000000 : ℝ)^8211 ≤ (13345242718311/100000000000000 : ℝ)^6163 := by
    have hnat : (441081519 : ℕ)^8211*100000000000000^6163 ≤ 13345242718311^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441081519 2000000000 13345242718311 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077520477/2000000000 : ℝ)^8211 ≤ (43866879684581/100000000000000 : ℝ)^6163 := by
    have hnat : (1077520477 : ℕ)^8211*100000000000000^6163 ≤ 43866879684581^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077520477 2000000000 43866879684581 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057565503/2000000000 : ℝ), (-441081519/2000000000 : ℝ), (1077520477/2000000000 : ℝ)] ![(10696969395337/25000000000000 : ℝ), (13345242718311/100000000000000 : ℝ), (43866879684581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057565503/2000000000 : ℝ)|^8211 ≤ (10696969395337/25000000000000 : ℝ)^6163
        have hw : |(1057565503/2000000000 : ℝ)|=(1057565503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441081519/2000000000 : ℝ)|^8211 ≤ (13345242718311/100000000000000 : ℝ)^6163
        have hw : |(-441081519/2000000000 : ℝ)|=(441081519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077520477/2000000000 : ℝ)|^8211 ≤ (43866879684581/100000000000000 : ℝ)^6163
        have hw : |(1077520477/2000000000 : ℝ)|=(1077520477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_10 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057565533/2000000000 : ℝ)*x 0 + (5387602511/10000000000 : ℝ)*x 1 + (-1102703613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057565533/2000000000 : ℝ)^8211 ≤ (21393939599227/50000000000000 : ℝ)^6163 := by
    have hnat : (1057565533 : ℕ)^8211*50000000000000^6163 ≤ 21393939599227^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057565533 2000000000 21393939599227 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387602511/10000000000 : ℝ)^8211 ≤ (8773376210283/20000000000000 : ℝ)^6163 := by
    have hnat : (5387602511 : ℕ)^8211*20000000000000^6163 ≤ 8773376210283^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387602511 10000000000 8773376210283 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102703613/5000000000 : ℝ)^8211 ≤ (6672619871721/50000000000000 : ℝ)^6163 := by
    have hnat : (1102703613 : ℕ)^8211*50000000000000^6163 ≤ 6672619871721^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102703613 5000000000 6672619871721 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057565533/2000000000 : ℝ), (5387602511/10000000000 : ℝ), (-1102703613/5000000000 : ℝ)] ![(21393939599227/50000000000000 : ℝ), (8773376210283/20000000000000 : ℝ), (6672619871721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057565533/2000000000 : ℝ)|^8211 ≤ (21393939599227/50000000000000 : ℝ)^6163
        have hw : |(1057565533/2000000000 : ℝ)|=(1057565533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387602511/10000000000 : ℝ)|^8211 ≤ (8773376210283/20000000000000 : ℝ)^6163
        have hw : |(5387602511/10000000000 : ℝ)|=(5387602511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102703613/5000000000 : ℝ)|^8211 ≤ (6672619871721/50000000000000 : ℝ)^6163
        have hw : |(-1102703613/5000000000 : ℝ)|=(1102703613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_11 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (902468207/2000000000 : ℝ)*x 0 + (431955099/1000000000 : ℝ)*x 1 + (4319550471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902468207/2000000000 : ℝ)^8211 ≤ (6927678095121/20000000000000 : ℝ)^6163 := by
    have hnat : (902468207 : ℕ)^8211*20000000000000^6163 ≤ 6927678095121^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902468207 2000000000 6927678095121 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431955099/1000000000 : ℝ)^8211 ≤ (6536161474461/20000000000000 : ℝ)^6163 := by
    have hnat : (431955099 : ℕ)^8211*20000000000000^6163 ≤ 6536161474461^6163*1000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431955099 1000000000 6536161474461 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319550471/10000000000 : ℝ)^8211 ≤ (6536160428163/20000000000000 : ℝ)^6163 := by
    have hnat : (4319550471 : ℕ)^8211*20000000000000^6163 ≤ 6536160428163^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319550471 10000000000 6536160428163 20000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(902468207/2000000000 : ℝ), (431955099/1000000000 : ℝ), (4319550471/10000000000 : ℝ)] ![(6927678095121/20000000000000 : ℝ), (6536161474461/20000000000000 : ℝ), (6536160428163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(902468207/2000000000 : ℝ)|^8211 ≤ (6927678095121/20000000000000 : ℝ)^6163
        have hw : |(902468207/2000000000 : ℝ)|=(902468207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431955099/1000000000 : ℝ)|^8211 ≤ (6536161474461/20000000000000 : ℝ)^6163
        have hw : |(431955099/1000000000 : ℝ)|=(431955099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319550471/10000000000 : ℝ)|^8211 ≤ (6536160428163/20000000000000 : ℝ)^6163
        have hw : |(4319550471/10000000000 : ℝ)|=(4319550471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_12 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151861759/10000000000 : ℝ)*x 0 + (544349269/1000000000 : ℝ)*x 1 + (5271363677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151861759/10000000000 : ℝ)^8211 ≤ (12915308439101/100000000000000 : ℝ)^6163 := by
    have hnat : (2151861759 : ℕ)^8211*100000000000000^6163 ≤ 12915308439101^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151861759 10000000000 12915308439101 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544349269/1000000000 : ℝ)^8211 ≤ (44474213943443/100000000000000 : ℝ)^6163 := by
    have hnat : (544349269 : ℕ)^8211*100000000000000^6163 ≤ 44474213943443^6163*1000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544349269 1000000000 44474213943443 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271363677/10000000000 : ℝ)^8211 ≤ (42610477608833/100000000000000 : ℝ)^6163 := by
    have hnat : (5271363677 : ℕ)^8211*100000000000000^6163 ≤ 42610477608833^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271363677 10000000000 42610477608833 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151861759/10000000000 : ℝ), (544349269/1000000000 : ℝ), (5271363677/10000000000 : ℝ)] ![(12915308439101/100000000000000 : ℝ), (44474213943443/100000000000000 : ℝ), (42610477608833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151861759/10000000000 : ℝ)|^8211 ≤ (12915308439101/100000000000000 : ℝ)^6163
        have hw : |(-2151861759/10000000000 : ℝ)|=(2151861759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544349269/1000000000 : ℝ)|^8211 ≤ (44474213943443/100000000000000 : ℝ)^6163
        have hw : |(544349269/1000000000 : ℝ)|=(544349269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271363677/10000000000 : ℝ)|^8211 ≤ (42610477608833/100000000000000 : ℝ)^6163
        have hw : |(5271363677/10000000000 : ℝ)|=(5271363677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_13 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685092319/5000000000 : ℝ)*x 0 + (-562670589/2500000000 : ℝ)*x 1 + (1054272749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685092319/5000000000 : ℝ)^8211 ≤ (436780355273/1000000000000 : ℝ)^6163 := by
    have hnat : (2685092319 : ℕ)^8211*1000000000000^6163 ≤ 436780355273^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685092319 5000000000 436780355273 1000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562670589/2500000000 : ℝ)^8211 ≤ (13711486119753/100000000000000 : ℝ)^6163 := by
    have hnat : (562670589 : ℕ)^8211*100000000000000^6163 ≤ 13711486119753^6163*2500000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562670589 2500000000 13711486119753 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054272749/2000000000 : ℝ)^8211 ≤ (21305239170581/50000000000000 : ℝ)^6163 := by
    have hnat : (1054272749 : ℕ)^8211*50000000000000^6163 ≤ 21305239170581^6163*2000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054272749 2000000000 21305239170581 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685092319/5000000000 : ℝ), (-562670589/2500000000 : ℝ), (1054272749/2000000000 : ℝ)] ![(436780355273/1000000000000 : ℝ), (13711486119753/100000000000000 : ℝ), (21305239170581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685092319/5000000000 : ℝ)|^8211 ≤ (436780355273/1000000000000 : ℝ)^6163
        have hw : |(2685092319/5000000000 : ℝ)|=(2685092319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562670589/2500000000 : ℝ)|^8211 ≤ (13711486119753/100000000000000 : ℝ)^6163
        have hw : |(-562670589/2500000000 : ℝ)|=(562670589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054272749/2000000000 : ℝ)|^8211 ≤ (21305239170581/50000000000000 : ℝ)^6163
        have hw : |(1054272749/2000000000 : ℝ)|=(1054272749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_14 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685092059/5000000000 : ℝ)*x 0 + (2635681999/5000000000 : ℝ)*x 1 + (-2250682713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685092059/5000000000 : ℝ)^8211 ≤ (43678029892467/100000000000000 : ℝ)^6163 := by
    have hnat : (2685092059 : ℕ)^8211*100000000000000^6163 ≤ 43678029892467^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685092059 5000000000 43678029892467 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635681999/5000000000 : ℝ)^8211 ≤ (42610481065857/100000000000000 : ℝ)^6163 := by
    have hnat : (2635681999 : ℕ)^8211*100000000000000^6163 ≤ 42610481065857^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635681999 5000000000 42610481065857 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250682713/10000000000 : ℝ)^8211 ≤ (13711489017379/100000000000000 : ℝ)^6163 := by
    have hnat : (2250682713 : ℕ)^8211*100000000000000^6163 ≤ 13711489017379^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250682713 10000000000 13711489017379 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685092059/5000000000 : ℝ), (2635681999/5000000000 : ℝ), (-2250682713/10000000000 : ℝ)] ![(43678029892467/100000000000000 : ℝ), (42610481065857/100000000000000 : ℝ), (13711489017379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685092059/5000000000 : ℝ)|^8211 ≤ (43678029892467/100000000000000 : ℝ)^6163
        have hw : |(2685092059/5000000000 : ℝ)|=(2685092059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635681999/5000000000 : ℝ)|^8211 ≤ (42610481065857/100000000000000 : ℝ)^6163
        have hw : |(2635681999/5000000000 : ℝ)|=(2635681999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2250682713/10000000000 : ℝ)|^8211 ≤ (13711489017379/100000000000000 : ℝ)^6163
        have hw : |(-2250682713/10000000000 : ℝ)|=(2250682713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1018_box_15 (p : ℝ) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4255314161/10000000000 : ℝ)*x 0 + (2224030683/5000000000 : ℝ)*x 1 + (4448061261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255314161/10000000000 : ℝ)^8211 ≤ (500545454139/1562500000000 : ℝ)^6163 := by
    have hnat : (4255314161 : ℕ)^8211*1562500000000^6163 ≤ 500545454139^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255314161 10000000000 500545454139 1562500000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224030683/5000000000 : ℝ)^8211 ≤ (33982545993569/100000000000000 : ℝ)^6163 := by
    have hnat : (2224030683 : ℕ)^8211*100000000000000^6163 ≤ 33982545993569^6163*5000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224030683 5000000000 33982545993569 100000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4448061261/10000000000 : ℝ)^8211 ≤ (16991272462407/50000000000000 : ℝ)^6163 := by
    have hnat : (4448061261 : ℕ)^8211*50000000000000^6163 ≤ 16991272462407^6163*10000000000^8211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448061261 10000000000 16991272462407 50000000000000 8211 6163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8211/2048 : ℝ)) 8211 6163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255314161/10000000000 : ℝ), (2224030683/5000000000 : ℝ), (4448061261/10000000000 : ℝ)] ![(500545454139/1562500000000 : ℝ), (33982545993569/100000000000000 : ℝ), (16991272462407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255314161/10000000000 : ℝ)|^8211 ≤ (500545454139/1562500000000 : ℝ)^6163
        have hw : |(4255314161/10000000000 : ℝ)|=(4255314161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2224030683/5000000000 : ℝ)|^8211 ≤ (33982545993569/100000000000000 : ℝ)^6163
        have hw : |(2224030683/5000000000 : ℝ)|=(2224030683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4448061261/10000000000 : ℝ)|^8211 ≤ (16991272462407/50000000000000 : ℝ)^6163
        have hw : |(4448061261/10000000000 : ℝ)|=(4448061261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1018_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147060167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11841/20000 : ℝ) ∧ (3971/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41421/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (699/6250 : ℝ) ^ (4105/1024 : ℝ) ≤ (7673556566292227/50000000000000000000 : ℝ) := by
    have hpowers : (699/6250 : ℝ)^4105 ≤ (7673556566292227/50000000000000000000 : ℝ)^1024 := by
      have hnat : (699 : ℕ)^4105*50000000000000000000^1024 ≤ 7673556566292227^1024*6250^4105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 6250 7673556566292227 50000000000000000000 4105 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/6250 : ℝ)) (X := (7673556566292227/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4105 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3493/25000 : ℝ) ^ (4105/1024 : ℝ) ≤ (1498241848146609/4000000000000000000 : ℝ) := by
    have hpowers : (3493/25000 : ℝ)^4105 ≤ (1498241848146609/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3493 : ℕ)^4105*4000000000000000000^1024 ≤ 1498241848146609^1024*25000^4105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3493 25000 1498241848146609 4000000000000000000 4105 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3493/25000 : ℝ)) (X := (1498241848146609/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4105 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007673556566292227/25000000000000000000 : ℝ) ≤ (1250095698136113/1250000000000000 : ℝ) ^ (4105/1024 : ℝ) := by
    have hpowers : (25007673556566292227/25000000000000000000 : ℝ)^1024 ≤ (1250095698136113/1250000000000000 : ℝ)^4105 := by
      have hnat : (25007673556566292227 : ℕ)^1024*1250000000000000^4105 ≤ 1250095698136113^4105*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007673556566292227 25000000000000000000 1250095698136113 1250000000000000 1024 4105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250095698136113/1250000000000000 : ℝ)) (X := (25007673556566292227/25000000000000000000 : ℝ)) (by norm_num) 4105 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052803159336249679/100000000000000000000 : ℝ) ≤ (10001316923850161/10000000000000000 : ℝ) ^ (4105/1024 : ℝ) := by
    have hpowers : (100052803159336249679/100000000000000000000 : ℝ)^1024 ≤ (10001316923850161/10000000000000000 : ℝ)^4105 := by
      have hnat : (100052803159336249679 : ℕ)^1024*10000000000000000^4105 ≤ 10001316923850161^4105*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052803159336249679 100000000000000000000 10001316923850161 10000000000000000 1024 4105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001316923850161/10000000000000000 : ℝ)) (X := (100052803159336249679/100000000000000000000 : ℝ)) (by norm_num) 4105 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001498241848146609/2000000000000000000 : ℝ) ≤ (5000934131305709/5000000000000000 : ℝ) ^ (4105/1024 : ℝ) := by
    have hpowers : (2001498241848146609/2000000000000000000 : ℝ)^1024 ≤ (5000934131305709/5000000000000000 : ℝ)^4105 := by
      have hnat : (2001498241848146609 : ℕ)^1024*5000000000000000^4105 ≤ 5000934131305709^4105*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001498241848146609 2000000000000000000 5000934131305709 5000000000000000 1024 4105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000934131305709/5000000000000000 : ℝ)) (X := (2001498241848146609/2000000000000000000 : ℝ)) (by norm_num) 4105 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7673556566292227/50000000000000000000 : ℝ) ≤ ((435465657903376059/435625000000000000 : ℝ)+2*(551338761257/278800000000000 : ℝ)*(699/6250 : ℝ))^(4105/1024 : ℝ) := by
    rw [show (435465657903376059/435625000000000000 : ℝ)+2*(551338761257/278800000000000 : ℝ)*(699/6250 : ℝ)=(1250095698136113/1250000000000000 : ℝ) by norm_num, show 1+2*(7673556566292227/50000000000000000000 : ℝ)=(25007673556566292227/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1498241848146609/4000000000000000000 : ℝ)+(7673556566292227/50000000000000000000 : ℝ) ≤ ((435465657903376059/435625000000000000 : ℝ)+(551338761257/278800000000000 : ℝ)*((3493/25000 : ℝ)+(699/6250 : ℝ)))^(4105/1024 : ℝ) := by
    rw [show (435465657903376059/435625000000000000 : ℝ)+(551338761257/278800000000000 : ℝ)*((3493/25000 : ℝ)+(699/6250 : ℝ))=(10001316923850161/10000000000000000 : ℝ) by norm_num, show 1+(1498241848146609/4000000000000000000 : ℝ)+(7673556566292227/50000000000000000000 : ℝ)=(100052803159336249679/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1498241848146609/4000000000000000000 : ℝ) ≤ ((435465657903376059/435625000000000000 : ℝ)+2*(551338761257/278800000000000 : ℝ)*(3493/25000 : ℝ))^(4105/1024 : ℝ) := by
    rw [show (435465657903376059/435625000000000000 : ℝ)+2*(551338761257/278800000000000 : ℝ)*(3493/25000 : ℝ)=(5000934131305709/5000000000000000 : ℝ) by norm_num, show 1+2*(1498241848146609/4000000000000000000 : ℝ)=(2001498241848146609/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (435465657903376059/435625000000000000 : ℝ)*(X 1 0+X 2 0)+(551338761257/278800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4105/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (435465657903376059/435625000000000000 : ℝ)) (alpha := (551338761257/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (435465657903376059/435625000000000000 : ℝ)*(X 0 1+X 2 1)+(551338761257/278800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4105/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (435465657903376059/435625000000000000 : ℝ)) (alpha := (551338761257/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (435465657903376059/435625000000000000 : ℝ)*(X 0 2+X 1 2)+(551338761257/278800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4105/1024 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (435465657903376059/435625000000000000 : ℝ)) (alpha := (551338761257/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096474681/10000000000 : ℝ)*X 0 0+(336125569/625000000 : ℝ)*X 0 1+(1344502187/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330914287/625000000 : ℝ)*X 1 0+(-2209214651/10000000000 : ℝ)*X 1 1+(2689004493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294628679/10000000000 : ℝ)*X 2 0+(2689004439/5000000000 : ℝ)*X 2 1+(-2209214679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4491397131/10000000000 : ℝ)*X 0 0+(4330163343/10000000000 : ℝ)*X 0 1+(433016307/1000000000 : ℝ)*X 0 2+(4491397131/10000000000 : ℝ)*X 1 0+(4330163343/10000000000 : ℝ)*X 1 1+(433016307/1000000000 : ℝ)*X 1 2+(4491397131/10000000000 : ℝ)*X 2 0+(4330163343/10000000000 : ℝ)*X 2 1+(433016307/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2360168137/10000000000 : ℝ)*X 0 0+(42234703/80000000 : ℝ)*X 0 1+(105586757/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072907483/2000000000 : ℝ)*X 1 0+(-561909197/2500000000 : ℝ)*X 1 1+(1319834437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364537097/10000000000 : ℝ)*X 2 0+(2639669001/5000000000 : ℝ)*X 2 1+(-3596219/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136589687/5000000000 : ℝ)*X 0 0+(4439250089/10000000000 : ℝ)*X 0 1+(4439250323/10000000000 : ℝ)*X 0 2+(2136589687/5000000000 : ℝ)*X 1 0+(4439250089/10000000000 : ℝ)*X 1 1+(4439250323/10000000000 : ℝ)*X 1 2+(2136589687/5000000000 : ℝ)*X 2 0+(4439250089/10000000000 : ℝ)*X 2 1+(4439250323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-288147797/1250000000 : ℝ)*X 0 0+(5212480149/10000000000 : ℝ)*X 0 1+(5387602403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057565503/2000000000 : ℝ)*X 1 0+(-441081519/2000000000 : ℝ)*X 1 1+(1077520477/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057565533/2000000000 : ℝ)*X 2 0+(5387602511/10000000000 : ℝ)*X 2 1+(-1102703613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((902468207/2000000000 : ℝ)*X 0 0+(431955099/1000000000 : ℝ)*X 0 1+(4319550471/10000000000 : ℝ)*X 0 2+(902468207/2000000000 : ℝ)*X 1 0+(431955099/1000000000 : ℝ)*X 1 1+(4319550471/10000000000 : ℝ)*X 1 2+(902468207/2000000000 : ℝ)*X 2 0+(431955099/1000000000 : ℝ)*X 2 1+(4319550471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2151861759/10000000000 : ℝ)*X 0 0+(544349269/1000000000 : ℝ)*X 0 1+(5271363677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2685092319/5000000000 : ℝ)*X 1 0+(-562670589/2500000000 : ℝ)*X 1 1+(1054272749/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2685092059/5000000000 : ℝ)*X 2 0+(2635681999/5000000000 : ℝ)*X 2 1+(-2250682713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4255314161/10000000000 : ℝ)*X 0 0+(2224030683/5000000000 : ℝ)*X 0 1+(4448061261/10000000000 : ℝ)*X 0 2+(4255314161/10000000000 : ℝ)*X 1 0+(2224030683/5000000000 : ℝ)*X 1 1+(4448061261/10000000000 : ℝ)*X 1 2+(4255314161/10000000000 : ℝ)*X 2 0+(2224030683/5000000000 : ℝ)*X 2 1+(4448061261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1018_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-52939053460462100757541446009/85083007812500000000000000000 : ℝ) := by norm_num
    linear_combination (47335123/100000000000000 : ℝ)*(upper1) + (1554921/1000000000000 : ℝ)*(upper2) + (109751/50000000000000 : ℝ)*(lower4) + (61260649/100000000000000 : ℝ)*(upper5) + (59619105999693/1562500000000 : ℝ)*(major0) + (59619105999693/1562500000000 : ℝ)*(major1) + (59619105999693/1562500000000 : ℝ)*(major2) + (215372441/50000000000000 : ℝ)*(sp1) + (70954721/4000000000000 : ℝ)*(sp3) + (2528692968570031/50000000000000 : ℝ)*(sp4) + (252869275319759/5000000000000 : ℝ)*(sp5) + (2528691107426321/50000000000000 : ℝ)*(sp6) + (1297299008006387/50000000000000 : ℝ)*(sp7) + (186114371/5000000000000 : ℝ)*(sp14) + (1297299894940399/50000000000000 : ℝ)*(f.failure) + (2528692968570031/50000000000000 : ℝ)*(f.sum) + (9955578634971/3485000000000000000000000000 : ℝ)*base65 + (101108826022411183/10890625000000000000000000000000 : ℝ)*base68 + (8956066273783923/2722656250000000000000000000000 : ℝ)*base69 + (3136686024723683/10890625000000000000000000000000 : ℝ)*base72 + (28349942384299/3485000000000000000000000000 : ℝ)*base74 + (22077043376815173/2722656250000000000000000000000 : ℝ)*base75 + (52055585802932567/10890625000000000000000000000000 : ℝ)*base77 + (16068219896057567/10890625000000000000000000000000 : ℝ)*base79 + (443171293373/1742500000000000000000000000 : ℝ)*base81 + (68013367/5000000000000000000000 : ℝ)*base90 + (68013367/5000000000000000000000 : ℝ)*base92 + (68013367/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (11841/20000 : ℝ) ≤ (6448103419347526859777664165033/10890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22733869/100000000000000 : ℝ)*(upper3) + (53987083/100000000000000 : ℝ)*(upper4) + (1720497/2500000000000 : ℝ)*(lower5) + (1938877751258257/50000000000000 : ℝ)*(major0) + (1938877751258257/50000000000000 : ℝ)*(major1) + (1938877751258257/50000000000000 : ℝ)*(major2) + (509891634923971/10000000000000 : ℝ)*(sp0) + (2549458146459493/50000000000000 : ℝ)*(sp1) + (101978298317201/2000000000000 : ℝ)*(sp2) + (659211158103109/25000000000000 : ℝ)*(sp3) + (1139272677/12500000000000 : ℝ)*(sp5) + (10491240353/100000000000000 : ℝ)*(sp6) + (5020095107/100000000000000 : ℝ)*(sp7) + (2264465173/25000000000000 : ℝ)*(sp8) + (329606206563443/12500000000000 : ℝ)*(f.failure) + (5098925407100403/100000000000000 : ℝ)*(f.sum) + (20417004151991/6970000000000000000000000000 : ℝ)*base66 + (526459815200328951/43562500000000000000000000000000 : ℝ)*base67 + (364557038728703951/43562500000000000000000000000000 : ℝ)*base69 + (398251001106641451/43562500000000000000000000000000 : ℝ)*base71 + (37472644881359/6970000000000000000000000000 : ℝ)*base73 + (246961228392703951/43562500000000000000000000000000 : ℝ)*base75 + (126102043495203951/43562500000000000000000000000000 : ℝ)*base77 + (426327241848703951/43562500000000000000000000000000 : ℝ)*base79 + (35186729674729/6970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1325019/1250000000000000000000 : ℝ)*base90 + (1325019/1250000000000000000000 : ℝ)*base92 + (1325019/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (3971/5000 : ℝ) ≤ (2214290156511153266182053567/2788000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55667/1562500000000 : ℝ)*(upper1) + (2664717/100000000000000 : ℝ)*(lower3) + (266035499/100000000000000 : ℝ)*(upper4) + (21374597/50000000000000 : ℝ)*(lower5) + (869205477482361/20000000000000 : ℝ)*(major0) + (869205477482361/20000000000000 : ℝ)*(major1) + (869205477482361/20000000000000 : ℝ)*(major2) + (2111370541/50000000000000 : ℝ)*(sp0) + (265226423937/100000000000000 : ℝ)*(sp2) + (48165317483/25000000000000 : ℝ)*(sp3) + (2855152434737427/50000000000000 : ℝ)*(sp8) + (5710309092215937/100000000000000 : ℝ)*(sp9) + (5710043865791999/100000000000000 : ℝ)*(sp10) + (738769740997659/25000000000000 : ℝ)*(sp11) + (369408953157571/12500000000000 : ℝ)*(f.failure) + (5710309092215937/100000000000000 : ℝ)*(f.sum) + (4790710704151/2788000000000000000000000000 : ℝ)*base66 + (289393772799556277/17425000000000000000000000000000 : ℝ)*base68 + (59643889445743723/17425000000000000000000000000000 : ℝ)*base69 + (142746781810781277/17425000000000000000000000000000 : ℝ)*base72 + (15069496265411/2788000000000000000000000000 : ℝ)*base74 + (163792533608231277/17425000000000000000000000000000 : ℝ)*base76 + (15645858261943723/17425000000000000000000000000000 : ℝ)*base77 + (79435305563018723/17425000000000000000000000000000 : ℝ)*base79 + (5407503437633/557600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6074357/1250000000000000000000 : ℝ)*base89 + (6074357/1250000000000000000000 : ℝ)*base91 + (6074357/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41421/50000 : ℝ) ≤ (-2255440234022461275747408220023/2722656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3412893/10000000000000 : ℝ)*(lower0) + (61165457/100000000000000 : ℝ)*(upper1) + (6192131/4000000000000 : ℝ)*(upper3) + (35114317/12500000000000 : ℝ)*(lower4) + (1095069255128309/25000000000000 : ℝ)*(major0) + (1095069255128309/25000000000000 : ℝ)*(major1) + (1095069255128309/25000000000000 : ℝ)*(major2) + (13577245193/20000000000000 : ℝ)*(sp5) + (30373332567/100000000000000 : ℝ)*(sp6) + (122560470199/100000000000000 : ℝ)*(sp7) + (5809606110919427/100000000000000 : ℝ)*(sp12) + (2904769112346731/50000000000000 : ℝ)*(sp13) + (5809575737586859/100000000000000 : ℝ)*(sp14) + (2978438602535441/100000000000000 : ℝ)*(sp15) + (74464029075141/2500000000000 : ℝ)*(f.failure) + (5809606110919427/100000000000000 : ℝ)*(f.sum) + (10640538594577/3485000000000000000000000000 : ℝ)*base66 + (92677967296794663/21781250000000000000000000000000 : ℝ)*base68 + (77086288792732163/21781250000000000000000000000000 : ℝ)*base70 + (310408001545763413/21781250000000000000000000000000 : ℝ)*base72 + (1458598433089/435625000000000000000000000 : ℝ)*base74 + (186996848946075913/21781250000000000000000000000000 : ℝ)*base76 + (21994326939825913/21781250000000000000000000000000 : ℝ)*base78 + (141126541541857163/21781250000000000000000000000000 : ℝ)*base80 + (10329451644797/3485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1008547/250000000000000000000 : ℝ)*base89 + (1008547/250000000000000000000 : ℝ)*base91 + (1008547/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1018_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147060167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (3971/5000 : ℝ) ≤ X j i ∧ X j i ≤ (41421/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1018_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4105/1024 : ℝ) ≤ p) (hpb : p ≤ (8211/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147060167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ) else (3971/5000 : ℝ) ≤ X j i ∧ X j i ≤ (41421/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1018_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
