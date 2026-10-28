-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1020_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:10:16.090404+00:00
-- url     : https://prove2.me/submissions/4c17453e-7531-48e3-b0b9-4be972339b83

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
theorem support_rectangle_w1020_box_0 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-41910987/200000000 : ℝ)*x 0 + (5377980533/10000000000 : ℝ)*x 1 + (134449507/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41910987/200000000 : ℝ)^8213 ≤ (12469082088543/100000000000000 : ℝ)^6165 := by
    have hnat : (41910987 : ℕ)^8213*100000000000000^6165 ≤ 12469082088543^6165*200000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41910987 200000000 12469082088543 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377980533/10000000000 : ℝ)^8213 ≤ (21882730161319/50000000000000 : ℝ)^6165 := by
    have hnat : (5377980533 : ℕ)^8213*50000000000000^6165 ≤ 21882730161319^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377980533 10000000000 21882730161319 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134449507/250000000 : ℝ)^8213 ≤ (43765457579791/100000000000000 : ℝ)^6165 := by
    have hnat : (134449507 : ℕ)^8213*100000000000000^6165 ≤ 43765457579791^6165*250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134449507 250000000 43765457579791 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41910987/200000000 : ℝ), (5377980533/10000000000 : ℝ), (134449507/250000000 : ℝ)] ![(12469082088543/100000000000000 : ℝ), (21882730161319/50000000000000 : ℝ), (43765457579791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41910987/200000000 : ℝ)|^8213 ≤ (12469082088543/100000000000000 : ℝ)^6165
        have hw : |(-41910987/200000000 : ℝ)|=(41910987/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377980533/10000000000 : ℝ)|^8213 ≤ (21882730161319/50000000000000 : ℝ)^6165
        have hw : |(5377980533/10000000000 : ℝ)|=(5377980533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134449507/250000000 : ℝ)|^8213 ≤ (43765457579791/100000000000000 : ℝ)^6165
        have hw : |(134449507/250000000 : ℝ)|=(134449507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_1 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661831869/1250000000 : ℝ)*x 0 + (-2208220799/10000000000 : ℝ)*x 1 + (1344495111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661831869/1250000000 : ℝ)^8213 ≤ (42864436289319/100000000000000 : ℝ)^6165 := by
    have hnat : (661831869 : ℕ)^8213*100000000000000^6165 ≤ 42864436289319^6165*1250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661831869 1250000000 42864436289319 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208220799/10000000000 : ℝ)^8213 ≤ (13370104341773/100000000000000 : ℝ)^6165 := by
    have hnat : (2208220799 : ℕ)^8213*100000000000000^6165 ≤ 13370104341773^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208220799 10000000000 13370104341773 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344495111/2500000000 : ℝ)^8213 ≤ (43765459357763/100000000000000 : ℝ)^6165 := by
    have hnat : (1344495111 : ℕ)^8213*100000000000000^6165 ≤ 43765459357763^6165*2500000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344495111 2500000000 43765459357763 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661831869/1250000000 : ℝ), (-2208220799/10000000000 : ℝ), (1344495111/2500000000 : ℝ)] ![(42864436289319/100000000000000 : ℝ), (13370104341773/100000000000000 : ℝ), (43765459357763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661831869/1250000000 : ℝ)|^8213 ≤ (42864436289319/100000000000000 : ℝ)^6165
        have hw : |(661831869/1250000000 : ℝ)|=(661831869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208220799/10000000000 : ℝ)|^8213 ≤ (13370104341773/100000000000000 : ℝ)^6165
        have hw : |(-2208220799/10000000000 : ℝ)|=(2208220799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344495111/2500000000 : ℝ)|^8213 ≤ (43765459357763/100000000000000 : ℝ)^6165
        have hw : |(1344495111/2500000000 : ℝ)|=(1344495111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_2 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647327507/5000000000 : ℝ)*x 0 + (5377980379/10000000000 : ℝ)*x 1 + (-552055201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647327507/5000000000 : ℝ)^8213 ≤ (42864436958001/100000000000000 : ℝ)^6165 := by
    have hnat : (2647327507 : ℕ)^8213*100000000000000^6165 ≤ 42864436958001^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647327507 5000000000 42864436958001 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377980379/10000000000 : ℝ)^8213 ≤ (43765458653079/100000000000000 : ℝ)^6165 := by
    have hnat : (5377980379 : ℕ)^8213*100000000000000^6165 ≤ 43765458653079^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377980379 10000000000 43765458653079 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552055201/2500000000 : ℝ)^8213 ≤ (13370104382103/100000000000000 : ℝ)^6165 := by
    have hnat : (552055201 : ℕ)^8213*100000000000000^6165 ≤ 13370104382103^6165*2500000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552055201 2500000000 13370104382103 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647327507/5000000000 : ℝ), (5377980379/10000000000 : ℝ), (-552055201/2500000000 : ℝ)] ![(42864436958001/100000000000000 : ℝ), (43765458653079/100000000000000 : ℝ), (13370104382103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647327507/5000000000 : ℝ)|^8213 ≤ (42864436958001/100000000000000 : ℝ)^6165
        have hw : |(2647327507/5000000000 : ℝ)|=(2647327507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377980379/10000000000 : ℝ)|^8213 ≤ (43765458653079/100000000000000 : ℝ)^6165
        have hw : |(5377980379/10000000000 : ℝ)|=(5377980379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-552055201/2500000000 : ℝ)|^8213 ≤ (13370104382103/100000000000000 : ℝ)^6165
        have hw : |(-552055201/2500000000 : ℝ)|=(552055201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_3 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (449107729/1000000000 : ℝ)*x 0 + (2164942337/5000000000 : ℝ)*x 1 + (4329884483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449107729/1000000000 : ℝ)^8213 ≤ (8606015357469/25000000000000 : ℝ)^6165 := by
    have hnat : (449107729 : ℕ)^8213*25000000000000^6165 ≤ 8606015357469^6165*1000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449107729 1000000000 8606015357469 25000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164942337/5000000000 : ℝ)^8213 ≤ (16393985119363/50000000000000 : ℝ)^6165 := by
    have hnat : (2164942337 : ℕ)^8213*50000000000000^6165 ≤ 16393985119363^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164942337 5000000000 16393985119363 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4329884483/10000000000 : ℝ)^8213 ≤ (3278796831191/10000000000000 : ℝ)^6165 := by
    have hnat : (4329884483 : ℕ)^8213*10000000000000^6165 ≤ 3278796831191^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329884483 10000000000 3278796831191 10000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449107729/1000000000 : ℝ), (2164942337/5000000000 : ℝ), (4329884483/10000000000 : ℝ)] ![(8606015357469/25000000000000 : ℝ), (16393985119363/50000000000000 : ℝ), (3278796831191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449107729/1000000000 : ℝ)|^8213 ≤ (8606015357469/25000000000000 : ℝ)^6165
        have hw : |(449107729/1000000000 : ℝ)|=(449107729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164942337/5000000000 : ℝ)|^8213 ≤ (16393985119363/50000000000000 : ℝ)^6165
        have hw : |(2164942337/5000000000 : ℝ)|=(2164942337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4329884483/10000000000 : ℝ)|^8213 ≤ (3278796831191/10000000000000 : ℝ)^6165
        have hw : |(4329884483/10000000000 : ℝ)|=(4329884483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_4 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-589772257/2500000000 : ℝ)*x 0 + (5279372463/10000000000 : ℝ)*x 1 + (527937227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (589772257/2500000000 : ℝ)^8213 ≤ (14600620741021/100000000000000 : ℝ)^6165 := by
    have hnat : (589772257 : ℕ)^8213*100000000000000^6165 ≤ 14600620741021^6165*2500000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589772257 2500000000 14600620741021 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279372463/10000000000 : ℝ)^8213 ≤ (42699690664093/100000000000000 : ℝ)^6165 := by
    have hnat : (5279372463 : ℕ)^8213*100000000000000^6165 ≤ 42699690664093^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279372463 10000000000 42699690664093 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527937227/1000000000 : ℝ)^8213 ≤ (10674922146137/25000000000000 : ℝ)^6165 := by
    have hnat : (527937227 : ℕ)^8213*25000000000000^6165 ≤ 10674922146137^6165*1000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527937227 1000000000 10674922146137 25000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-589772257/2500000000 : ℝ), (5279372463/10000000000 : ℝ), (527937227/1000000000 : ℝ)] ![(14600620741021/100000000000000 : ℝ), (42699690664093/100000000000000 : ℝ), (10674922146137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-589772257/2500000000 : ℝ)|^8213 ≤ (14600620741021/100000000000000 : ℝ)^6165
        have hw : |(-589772257/2500000000 : ℝ)|=(589772257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279372463/10000000000 : ℝ)|^8213 ≤ (42699690664093/100000000000000 : ℝ)^6165
        have hw : |(5279372463/10000000000 : ℝ)|=(5279372463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527937227/1000000000 : ℝ)|^8213 ≤ (10674922146137/25000000000000 : ℝ)^6165
        have hw : |(527937227/1000000000 : ℝ)|=(527937227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_5 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341128919/2500000000 : ℝ)*x 0 + (-1123312443/5000000000 : ℝ)*x 1 + (659921553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341128919/2500000000 : ℝ)^8213 ≤ (21809772312277/50000000000000 : ℝ)^6165 := by
    have hnat : (1341128919 : ℕ)^8213*50000000000000^6165 ≤ 21809772312277^6165*2500000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341128919 2500000000 21809772312277 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123312443/5000000000 : ℝ)^8213 ≤ (85504781953/625000000000 : ℝ)^6165 := by
    have hnat : (1123312443 : ℕ)^8213*625000000000^6165 ≤ 85504781953^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123312443 5000000000 85504781953 625000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659921553/1250000000 : ℝ)^8213 ≤ (21349845121937/50000000000000 : ℝ)^6165 := by
    have hnat : (659921553 : ℕ)^8213*50000000000000^6165 ≤ 21349845121937^6165*1250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659921553 1250000000 21349845121937 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341128919/2500000000 : ℝ), (-1123312443/5000000000 : ℝ), (659921553/1250000000 : ℝ)] ![(21809772312277/50000000000000 : ℝ), (85504781953/625000000000 : ℝ), (21349845121937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341128919/2500000000 : ℝ)|^8213 ≤ (21809772312277/50000000000000 : ℝ)^6165
        have hw : |(1341128919/2500000000 : ℝ)|=(1341128919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123312443/5000000000 : ℝ)|^8213 ≤ (85504781953/625000000000 : ℝ)^6165
        have hw : |(-1123312443/5000000000 : ℝ)|=(1123312443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659921553/1250000000 : ℝ)|^8213 ≤ (21349845121937/50000000000000 : ℝ)^6165
        have hw : |(659921553/1250000000 : ℝ)|=(659921553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_6 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682257981/5000000000 : ℝ)*x 0 + (5279372233/10000000000 : ℝ)*x 1 + (-1123312379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682257981/5000000000 : ℝ)^8213 ≤ (43619547722583/100000000000000 : ℝ)^6165 := by
    have hnat : (2682257981 : ℕ)^8213*100000000000000^6165 ≤ 43619547722583^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682257981 5000000000 43619547722583 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279372233/10000000000 : ℝ)^8213 ≤ (21349844092939/50000000000000 : ℝ)^6165 := by
    have hnat : (5279372233 : ℕ)^8213*50000000000000^6165 ≤ 21349844092939^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279372233 10000000000 21349844092939 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123312379/5000000000 : ℝ)^8213 ≤ (6840382037047/50000000000000 : ℝ)^6165 := by
    have hnat : (1123312379 : ℕ)^8213*50000000000000^6165 ≤ 6840382037047^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123312379 5000000000 6840382037047 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682257981/5000000000 : ℝ), (5279372233/10000000000 : ℝ), (-1123312379/5000000000 : ℝ)] ![(43619547722583/100000000000000 : ℝ), (21349844092939/50000000000000 : ℝ), (6840382037047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682257981/5000000000 : ℝ)|^8213 ≤ (43619547722583/100000000000000 : ℝ)^6165
        have hw : |(2682257981/5000000000 : ℝ)|=(2682257981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279372233/10000000000 : ℝ)|^8213 ≤ (21349844092939/50000000000000 : ℝ)^6165
        have hw : |(5279372233/10000000000 : ℝ)|=(5279372233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123312379/5000000000 : ℝ)|^8213 ≤ (6840382037047/50000000000000 : ℝ)^6165
        have hw : |(-1123312379/5000000000 : ℝ)|=(1123312379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_7 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2136458083/5000000000 : ℝ)*x 0 + (4438943227/10000000000 : ℝ)*x 1 + (4438943341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136458083/5000000000 : ℝ)^8213 ≤ (32214529087303/100000000000000 : ℝ)^6165 := by
    have hnat : (2136458083 : ℕ)^8213*100000000000000^6165 ≤ 32214529087303^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136458083 5000000000 32214529087303 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4438943227/10000000000 : ℝ)^8213 ≤ (33892734868673/100000000000000 : ℝ)^6165 := by
    have hnat : (4438943227 : ℕ)^8213*100000000000000^6165 ≤ 33892734868673^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438943227 10000000000 33892734868673 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4438943341/10000000000 : ℝ)^8213 ≤ (33892736028253/100000000000000 : ℝ)^6165 := by
    have hnat : (4438943341 : ℕ)^8213*100000000000000^6165 ≤ 33892736028253^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438943341 10000000000 33892736028253 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136458083/5000000000 : ℝ), (4438943227/10000000000 : ℝ), (4438943341/10000000000 : ℝ)] ![(32214529087303/100000000000000 : ℝ), (33892734868673/100000000000000 : ℝ), (33892736028253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136458083/5000000000 : ℝ)|^8213 ≤ (32214529087303/100000000000000 : ℝ)^6165
        have hw : |(2136458083/5000000000 : ℝ)|=(2136458083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4438943227/10000000000 : ℝ)|^8213 ≤ (33892734868673/100000000000000 : ℝ)^6165
        have hw : |(4438943227/10000000000 : ℝ)|=(4438943227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4438943341/10000000000 : ℝ)|^8213 ≤ (33892736028253/100000000000000 : ℝ)^6165
        have hw : |(4438943341/10000000000 : ℝ)|=(4438943341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_8 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-230413261/1000000000 : ℝ)*x 0 + (1042510679/2000000000 : ℝ)*x 1 + (2693786901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230413261/1000000000 : ℝ)^8213 ≤ (2829852452073/20000000000000 : ℝ)^6165 := by
    have hnat : (230413261 : ℕ)^8213*20000000000000^6165 ≤ 2829852452073^6165*1000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230413261 1000000000 2829852452073 20000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042510679/2000000000 : ℝ)^8213 ≤ (41981243173271/100000000000000 : ℝ)^6165 := by
    have hnat : (1042510679 : ℕ)^8213*100000000000000^6165 ≤ 41981243173271^6165*2000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042510679 2000000000 41981243173271 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693786901/5000000000 : ℝ)^8213 ≤ (21934747274919/50000000000000 : ℝ)^6165 := by
    have hnat : (2693786901 : ℕ)^8213*50000000000000^6165 ≤ 21934747274919^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693786901 5000000000 21934747274919 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230413261/1000000000 : ℝ), (1042510679/2000000000 : ℝ), (2693786901/5000000000 : ℝ)] ![(2829852452073/20000000000000 : ℝ), (41981243173271/100000000000000 : ℝ), (21934747274919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230413261/1000000000 : ℝ)|^8213 ≤ (2829852452073/20000000000000 : ℝ)^6165
        have hw : |(-230413261/1000000000 : ℝ)|=(230413261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042510679/2000000000 : ℝ)|^8213 ≤ (41981243173271/100000000000000 : ℝ)^6165
        have hw : |(1042510679/2000000000 : ℝ)|=(1042510679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693786901/5000000000 : ℝ)|^8213 ≤ (21934747274919/50000000000000 : ℝ)^6165
        have hw : |(2693786901/5000000000 : ℝ)|=(2693786901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_9 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660981777/1250000000 : ℝ)*x 0 + (-2204413247/10000000000 : ℝ)*x 1 + (2693786881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660981777/1250000000 : ℝ)^8213 ≤ (10697776161371/25000000000000 : ℝ)^6165 := by
    have hnat : (660981777 : ℕ)^8213*25000000000000^6165 ≤ 10697776161371^6165*1250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660981777 1250000000 10697776161371 25000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204413247/10000000000 : ℝ)^8213 ≤ (6669700613403/50000000000000 : ℝ)^6165 := by
    have hnat : (2204413247 : ℕ)^8213*50000000000000^6165 ≤ 6669700613403^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204413247 10000000000 6669700613403 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693786881/5000000000 : ℝ)^8213 ≤ (43869494115929/100000000000000 : ℝ)^6165 := by
    have hnat : (2693786881 : ℕ)^8213*100000000000000^6165 ≤ 43869494115929^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693786881 5000000000 43869494115929 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660981777/1250000000 : ℝ), (-2204413247/10000000000 : ℝ), (2693786881/5000000000 : ℝ)] ![(10697776161371/25000000000000 : ℝ), (6669700613403/50000000000000 : ℝ), (43869494115929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660981777/1250000000 : ℝ)|^8213 ≤ (10697776161371/25000000000000 : ℝ)^6165
        have hw : |(660981777/1250000000 : ℝ)|=(660981777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204413247/10000000000 : ℝ)|^8213 ≤ (6669700613403/50000000000000 : ℝ)^6165
        have hw : |(-2204413247/10000000000 : ℝ)|=(2204413247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693786881/5000000000 : ℝ)|^8213 ≤ (43869494115929/100000000000000 : ℝ)^6165
        have hw : |(2693786881/5000000000 : ℝ)|=(2693786881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_10 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287854393/10000000000 : ℝ)*x 0 + (5387573913/10000000000 : ℝ)*x 1 + (-1102206403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287854393/10000000000 : ℝ)^8213 ≤ (855822131073/2000000000000 : ℝ)^6165 := by
    have hnat : (5287854393 : ℕ)^8213*2000000000000^6165 ≤ 855822131073^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287854393 10000000000 855822131073 2000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387573913/10000000000 : ℝ)^8213 ≤ (21934747876967/50000000000000 : ℝ)^6165 := by
    have hnat : (5387573913 : ℕ)^8213*50000000000000^6165 ≤ 21934747876967^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387573913 10000000000 21934747876967 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102206403/5000000000 : ℝ)^8213 ≤ (2667879534343/20000000000000 : ℝ)^6165 := by
    have hnat : (1102206403 : ℕ)^8213*20000000000000^6165 ≤ 2667879534343^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102206403 5000000000 2667879534343 20000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287854393/10000000000 : ℝ), (5387573913/10000000000 : ℝ), (-1102206403/5000000000 : ℝ)] ![(855822131073/2000000000000 : ℝ), (21934747876967/50000000000000 : ℝ), (2667879534343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287854393/10000000000 : ℝ)|^8213 ≤ (855822131073/2000000000000 : ℝ)^6165
        have hw : |(5287854393/10000000000 : ℝ)|=(5287854393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387573913/10000000000 : ℝ)|^8213 ≤ (21934747876967/50000000000000 : ℝ)^6165
        have hw : |(5387573913/10000000000 : ℝ)|=(5387573913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102206403/5000000000 : ℝ)|^8213 ≤ (2667879534343/20000000000000 : ℝ)^6165
        have hw : |(-1102206403/5000000000 : ℝ)|=(1102206403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_11 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4512029029/10000000000 : ℝ)*x 0 + (2159634221/5000000000 : ℝ)*x 1 + (4319267953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4512029029/10000000000 : ℝ)^8213 ≤ (17319085590071/50000000000000 : ℝ)^6165 := by
    have hnat : (4512029029 : ℕ)^8213*50000000000000^6165 ≤ 17319085590071^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512029029 10000000000 17319085590071 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159634221/5000000000 : ℝ)^8213 ≤ (32680916867891/100000000000000 : ℝ)^6165 := by
    have hnat : (2159634221 : ℕ)^8213*100000000000000^6165 ≤ 32680916867891^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159634221 5000000000 32680916867891 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319267953/10000000000 : ℝ)^8213 ≤ (32680911938859/100000000000000 : ℝ)^6165 := by
    have hnat : (4319267953 : ℕ)^8213*100000000000000^6165 ≤ 32680911938859^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319267953 10000000000 32680911938859 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4512029029/10000000000 : ℝ), (2159634221/5000000000 : ℝ), (4319267953/10000000000 : ℝ)] ![(17319085590071/50000000000000 : ℝ), (32680916867891/100000000000000 : ℝ), (32680911938859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4512029029/10000000000 : ℝ)|^8213 ≤ (17319085590071/50000000000000 : ℝ)^6165
        have hw : |(4512029029/10000000000 : ℝ)|=(4512029029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2159634221/5000000000 : ℝ)|^8213 ≤ (32680916867891/100000000000000 : ℝ)^6165
        have hw : |(2159634221/5000000000 : ℝ)|=(2159634221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319267953/10000000000 : ℝ)|^8213 ≤ (32680911938859/100000000000000 : ℝ)^6165
        have hw : |(4319267953/10000000000 : ℝ)|=(4319267953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_12 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-268863211/1250000000 : ℝ)*x 0 + (5443427041/10000000000 : ℝ)*x 1 + (5271397417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268863211/1250000000 : ℝ)^8213 ≤ (2581960473319/20000000000000 : ℝ)^6165 := by
    have hnat : (268863211 : ℕ)^8213*20000000000000^6165 ≤ 2581960473319^6165*1250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268863211 1250000000 2581960473319 20000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443427041/10000000000 : ℝ)^8213 ≤ (22238207646503/50000000000000 : ℝ)^6165 := by
    have hnat : (5443427041 : ℕ)^8213*50000000000000^6165 ≤ 22238207646503^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443427041 10000000000 22238207646503 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271397417/10000000000 : ℝ)^8213 ≤ (4261378232049/10000000000000 : ℝ)^6165 := by
    have hnat : (5271397417 : ℕ)^8213*10000000000000^6165 ≤ 4261378232049^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271397417 10000000000 4261378232049 10000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268863211/1250000000 : ℝ), (5443427041/10000000000 : ℝ), (5271397417/10000000000 : ℝ)] ![(2581960473319/20000000000000 : ℝ), (22238207646503/50000000000000 : ℝ), (4261378232049/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268863211/1250000000 : ℝ)|^8213 ≤ (2581960473319/20000000000000 : ℝ)^6165
        have hw : |(-268863211/1250000000 : ℝ)|=(268863211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443427041/10000000000 : ℝ)|^8213 ≤ (22238207646503/50000000000000 : ℝ)^6165
        have hw : |(5443427041/10000000000 : ℝ)|=(5443427041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271397417/10000000000 : ℝ)|^8213 ≤ (4261378232049/10000000000000 : ℝ)^6165
        have hw : |(5271397417/10000000000 : ℝ)|=(5271397417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_13 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370163413/10000000000 : ℝ)*x 0 + (-140604471/625000000 : ℝ)*x 1 + (658924657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370163413/10000000000 : ℝ)^8213 ≤ (43680733114429/100000000000000 : ℝ)^6165 := by
    have hnat : (5370163413 : ℕ)^8213*100000000000000^6165 ≤ 43680733114429^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370163413 10000000000 43680733114429 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140604471/625000000 : ℝ)^8213 ≤ (13705486276227/100000000000000 : ℝ)^6165 := by
    have hnat : (140604471 : ℕ)^8213*100000000000000^6165 ≤ 13705486276227^6165*625000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140604471 625000000 13705486276227 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658924657/1250000000 : ℝ)^8213 ≤ (4261378058661/10000000000000 : ℝ)^6165 := by
    have hnat : (658924657 : ℕ)^8213*10000000000000^6165 ≤ 4261378058661^6165*1250000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658924657 1250000000 4261378058661 10000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370163413/10000000000 : ℝ), (-140604471/625000000 : ℝ), (658924657/1250000000 : ℝ)] ![(43680733114429/100000000000000 : ℝ), (13705486276227/100000000000000 : ℝ), (4261378058661/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370163413/10000000000 : ℝ)|^8213 ≤ (43680733114429/100000000000000 : ℝ)^6165
        have hw : |(5370163413/10000000000 : ℝ)|=(5370163413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140604471/625000000 : ℝ)|^8213 ≤ (13705486276227/100000000000000 : ℝ)^6165
        have hw : |(-140604471/625000000 : ℝ)|=(140604471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658924657/1250000000 : ℝ)|^8213 ≤ (4261378058661/10000000000000 : ℝ)^6165
        have hw : |(658924657/1250000000 : ℝ)|=(658924657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_14 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26850817/50000000 : ℝ)*x 0 + (2635698651/5000000000 : ℝ)*x 1 + (-2249671493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26850817/50000000 : ℝ)^8213 ≤ (43680732973561/100000000000000 : ℝ)^6165 := by
    have hnat : (26850817 : ℕ)^8213*100000000000000^6165 ≤ 43680732973561^6165*50000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26850817 50000000 43680732973561 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635698651/5000000000 : ℝ)^8213 ≤ (10653445270501/25000000000000 : ℝ)^6165 := by
    have hnat : (2635698651 : ℕ)^8213*25000000000000^6165 ≤ 10653445270501^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635698651 5000000000 10653445270501 25000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249671493/10000000000 : ℝ)^8213 ≤ (6852742963619/50000000000000 : ℝ)^6165 := by
    have hnat : (2249671493 : ℕ)^8213*50000000000000^6165 ≤ 6852742963619^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249671493 10000000000 6852742963619 50000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26850817/50000000 : ℝ), (2635698651/5000000000 : ℝ), (-2249671493/10000000000 : ℝ)] ![(43680732973561/100000000000000 : ℝ), (10653445270501/25000000000000 : ℝ), (6852742963619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26850817/50000000 : ℝ)|^8213 ≤ (43680732973561/100000000000000 : ℝ)^6165
        have hw : |(26850817/50000000 : ℝ)|=(26850817/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635698651/5000000000 : ℝ)|^8213 ≤ (10653445270501/25000000000000 : ℝ)^6165
        have hw : |(2635698651/5000000000 : ℝ)|=(2635698651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2249671493/10000000000 : ℝ)|^8213 ≤ (6852742963619/50000000000000 : ℝ)^6165
        have hw : |(-2249671493/10000000000 : ℝ)|=(2249671493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1020_box_15 (p : ℝ) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4255042147/10000000000 : ℝ)*x 0 + (2223879391/5000000000 : ℝ)*x 1 + (11119397/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255042147/10000000000 : ℝ)^8213 ≤ (640702633003/2000000000000 : ℝ)^6165 := by
    have hnat : (4255042147 : ℕ)^8213*2000000000000^6165 ≤ 640702633003^6165*10000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255042147 10000000000 640702633003 2000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223879391/5000000000 : ℝ)^8213 ≤ (33982434074283/100000000000000 : ℝ)^6165 := by
    have hnat : (2223879391 : ℕ)^8213*100000000000000^6165 ≤ 33982434074283^6165*5000000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223879391 5000000000 33982434074283 100000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11119397/25000000 : ℝ)^8213 ≤ (6796486851499/20000000000000 : ℝ)^6165 := by
    have hnat : (11119397 : ℕ)^8213*20000000000000^6165 ≤ 6796486851499^6165*25000000^8213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11119397 25000000 6796486851499 20000000000000 8213 6165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8213/2048 : ℝ)) 8213 6165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255042147/10000000000 : ℝ), (2223879391/5000000000 : ℝ), (11119397/25000000 : ℝ)] ![(640702633003/2000000000000 : ℝ), (33982434074283/100000000000000 : ℝ), (6796486851499/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255042147/10000000000 : ℝ)|^8213 ≤ (640702633003/2000000000000 : ℝ)^6165
        have hw : |(4255042147/10000000000 : ℝ)|=(4255042147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2223879391/5000000000 : ℝ)|^8213 ≤ (33982434074283/100000000000000 : ℝ)^6165
        have hw : |(2223879391/5000000000 : ℝ)|=(2223879391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11119397/25000000 : ℝ)|^8213 ≤ (6796486851499/20000000000000 : ℝ)^6165
        have hw : |(11119397/25000000 : ℝ)|=(11119397/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1020_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147099001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13973/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59207/100000 : ℝ) ∧ (39713/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82847/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13973/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13973/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13973/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13973/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13973/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13973/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11187/100000 : ℝ) ^ (2053/512 : ℝ) ≤ (479087310715913/3125000000000000000 : ℝ) := by
    have hpowers : (11187/100000 : ℝ)^2053 ≤ (479087310715913/3125000000000000000 : ℝ)^512 := by
      have hnat : (11187 : ℕ)^2053*3125000000000000000^512 ≤ 479087310715913^512*100000^2053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11187 100000 479087310715913 3125000000000000000 2053 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11187/100000 : ℝ)) (X := (479087310715913/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2053 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13973/100000 : ℝ) ^ (2053/512 : ℝ) ≤ (37394855169993133/100000000000000000000 : ℝ) := by
    have hpowers : (13973/100000 : ℝ)^2053 ≤ (37394855169993133/100000000000000000000 : ℝ)^512 := by
      have hnat : (13973 : ℕ)^2053*100000000000000000000^512 ≤ 37394855169993133^512*100000^2053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13973 100000 37394855169993133 100000000000000000000 2053 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13973/100000 : ℝ)) (X := (37394855169993133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2053 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562979087310715913/1562500000000000000 : ℝ) ≤ (312523893276303/312500000000000 : ℝ) ^ (2053/512 : ℝ) := by
    have hpowers : (1562979087310715913/1562500000000000000 : ℝ)^512 ≤ (312523893276303/312500000000000 : ℝ)^2053 := by
      have hnat : (1562979087310715913 : ℕ)^512*312500000000000^2053 ≤ 312523893276303^2053*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562979087310715913 1562500000000000000 312523893276303 312500000000000 512 2053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312523893276303/312500000000000 : ℝ)) (X := (1562979087310715913/1562500000000000000 : ℝ)) (by norm_num) 2053 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052725649112902349/100000000000000000000 : ℝ) ≤ (10001314670826449/10000000000000000 : ℝ) ^ (2053/512 : ℝ) := by
    have hpowers : (100052725649112902349/100000000000000000000 : ℝ)^512 ≤ (10001314670826449/10000000000000000 : ℝ)^2053 := by
      have hnat : (100052725649112902349 : ℕ)^512*10000000000000000^2053 ≤ 10001314670826449^2053*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052725649112902349 100000000000000000000 10001314670826449 10000000000000000 512 2053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001314670826449/10000000000000000 : ℝ)) (X := (100052725649112902349/100000000000000000000 : ℝ)) (by norm_num) 2053 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037394855169993133/50000000000000000000 : ℝ) ≤ (5000932378405601/5000000000000000 : ℝ) ^ (2053/512 : ℝ) := by
    have hpowers : (50037394855169993133/50000000000000000000 : ℝ)^512 ≤ (5000932378405601/5000000000000000 : ℝ)^2053 := by
      have hnat : (50037394855169993133 : ℕ)^512*5000000000000000^2053 ≤ 5000932378405601^2053*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037394855169993133 50000000000000000000 5000932378405601 5000000000000000 512 2053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000932378405601/5000000000000000 : ℝ)) (X := (50037394855169993133/50000000000000000000 : ℝ)) (by norm_num) 2053 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(479087310715913/3125000000000000000 : ℝ) ≤ ((13924911254773050717/13930000000000000000 : ℝ)+2*(550085984753/278600000000000 : ℝ)*(11187/100000 : ℝ))^(2053/512 : ℝ) := by
    rw [show (13924911254773050717/13930000000000000000 : ℝ)+2*(550085984753/278600000000000 : ℝ)*(11187/100000 : ℝ)=(312523893276303/312500000000000 : ℝ) by norm_num, show 1+2*(479087310715913/3125000000000000000 : ℝ)=(1562979087310715913/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37394855169993133/100000000000000000000 : ℝ)+(479087310715913/3125000000000000000 : ℝ) ≤ ((13924911254773050717/13930000000000000000 : ℝ)+(550085984753/278600000000000 : ℝ)*((13973/100000 : ℝ)+(11187/100000 : ℝ)))^(2053/512 : ℝ) := by
    rw [show (13924911254773050717/13930000000000000000 : ℝ)+(550085984753/278600000000000 : ℝ)*((13973/100000 : ℝ)+(11187/100000 : ℝ))=(10001314670826449/10000000000000000 : ℝ) by norm_num, show 1+(37394855169993133/100000000000000000000 : ℝ)+(479087310715913/3125000000000000000 : ℝ)=(100052725649112902349/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37394855169993133/100000000000000000000 : ℝ) ≤ ((13924911254773050717/13930000000000000000 : ℝ)+2*(550085984753/278600000000000 : ℝ)*(13973/100000 : ℝ))^(2053/512 : ℝ) := by
    rw [show (13924911254773050717/13930000000000000000 : ℝ)+2*(550085984753/278600000000000 : ℝ)*(13973/100000 : ℝ)=(5000932378405601/5000000000000000 : ℝ) by norm_num, show 1+2*(37394855169993133/100000000000000000000 : ℝ)=(50037394855169993133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13924911254773050717/13930000000000000000 : ℝ)*(X 1 0+X 2 0)+(550085984753/278600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2053/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (13973/100000 : ℝ)) (c := (13924911254773050717/13930000000000000000 : ℝ)) (alpha := (550085984753/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13924911254773050717/13930000000000000000 : ℝ)*(X 0 1+X 2 1)+(550085984753/278600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2053/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (13973/100000 : ℝ)) (c := (13924911254773050717/13930000000000000000 : ℝ)) (alpha := (550085984753/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13924911254773050717/13930000000000000000 : ℝ)*(X 0 2+X 1 2)+(550085984753/278600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2053/512 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (13973/100000 : ℝ)) (c := (13924911254773050717/13930000000000000000 : ℝ)) (alpha := (550085984753/278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-41910987/200000000 : ℝ)*X 0 0+(5377980533/10000000000 : ℝ)*X 0 1+(134449507/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661831869/1250000000 : ℝ)*X 1 0+(-2208220799/10000000000 : ℝ)*X 1 1+(1344495111/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647327507/5000000000 : ℝ)*X 2 0+(5377980379/10000000000 : ℝ)*X 2 1+(-552055201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((449107729/1000000000 : ℝ)*X 0 0+(2164942337/5000000000 : ℝ)*X 0 1+(4329884483/10000000000 : ℝ)*X 0 2+(449107729/1000000000 : ℝ)*X 1 0+(2164942337/5000000000 : ℝ)*X 1 1+(4329884483/10000000000 : ℝ)*X 1 2+(449107729/1000000000 : ℝ)*X 2 0+(2164942337/5000000000 : ℝ)*X 2 1+(4329884483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-589772257/2500000000 : ℝ)*X 0 0+(5279372463/10000000000 : ℝ)*X 0 1+(527937227/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1341128919/2500000000 : ℝ)*X 1 0+(-1123312443/5000000000 : ℝ)*X 1 1+(659921553/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682257981/5000000000 : ℝ)*X 2 0+(5279372233/10000000000 : ℝ)*X 2 1+(-1123312379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136458083/5000000000 : ℝ)*X 0 0+(4438943227/10000000000 : ℝ)*X 0 1+(4438943341/10000000000 : ℝ)*X 0 2+(2136458083/5000000000 : ℝ)*X 1 0+(4438943227/10000000000 : ℝ)*X 1 1+(4438943341/10000000000 : ℝ)*X 1 2+(2136458083/5000000000 : ℝ)*X 2 0+(4438943227/10000000000 : ℝ)*X 2 1+(4438943341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-230413261/1000000000 : ℝ)*X 0 0+(1042510679/2000000000 : ℝ)*X 0 1+(2693786901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((660981777/1250000000 : ℝ)*X 1 0+(-2204413247/10000000000 : ℝ)*X 1 1+(2693786881/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287854393/10000000000 : ℝ)*X 2 0+(5387573913/10000000000 : ℝ)*X 2 1+(-1102206403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4512029029/10000000000 : ℝ)*X 0 0+(2159634221/5000000000 : ℝ)*X 0 1+(4319267953/10000000000 : ℝ)*X 0 2+(4512029029/10000000000 : ℝ)*X 1 0+(2159634221/5000000000 : ℝ)*X 1 1+(4319267953/10000000000 : ℝ)*X 1 2+(4512029029/10000000000 : ℝ)*X 2 0+(2159634221/5000000000 : ℝ)*X 2 1+(4319267953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-268863211/1250000000 : ℝ)*X 0 0+(5443427041/10000000000 : ℝ)*X 0 1+(5271397417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370163413/10000000000 : ℝ)*X 1 0+(-140604471/625000000 : ℝ)*X 1 1+(658924657/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((26850817/50000000 : ℝ)*X 2 0+(2635698651/5000000000 : ℝ)*X 2 1+(-2249671493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4255042147/10000000000 : ℝ)*X 0 0+(2223879391/5000000000 : ℝ)*X 0 1+(11119397/25000000 : ℝ)*X 0 2+(4255042147/10000000000 : ℝ)*X 1 0+(2223879391/5000000000 : ℝ)*X 1 1+(11119397/25000000 : ℝ)*X 1 2+(4255042147/10000000000 : ℝ)*X 2 0+(2223879391/5000000000 : ℝ)*X 2 1+(11119397/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1020_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-108341347753228648152977304601281/174125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69782959/100000000000000 : ℝ)*(upper0) + (117909283/100000000000000 : ℝ)*(lower2) + (2539/4000000000000 : ℝ)*(upper4) + (3928651/10000000000000 : ℝ)*(upper5) + (1908743350105369/50000000000000 : ℝ)*(major0) + (1908743350105369/50000000000000 : ℝ)*(major1) + (1908743350105369/50000000000000 : ℝ)*(major2) + (3830244023/100000000000000 : ℝ)*(sp2) + (396495551/20000000000000 : ℝ)*(sp3) + (1265131102764417/25000000000000 : ℝ)*(sp4) + (506053161356073/10000000000000 : ℝ)*(sp5) + (5060527783316707/100000000000000 : ℝ)*(sp6) + (648794988078431/25000000000000 : ℝ)*(sp7) + (3601251531/50000000000000 : ℝ)*(sp8) + (64879548369787/2500000000000 : ℝ)*(f.failure) + (506053161356073/10000000000000 : ℝ)*(f.sum) + (94023486864793/6965000000000000000000000000 : ℝ)*base66 + (6845800827954150427/696500000000000000000000000000000 : ℝ)*base68 + (1952031382910650427/696500000000000000000000000000000 : ℝ)*base70 + (601388320677150427/696500000000000000000000000000000 : ℝ)*base72 + (70362912033187/6965000000000000000000000000 : ℝ)*base73 + (4003405973084650427/696500000000000000000000000000000 : ℝ)*base76 + (11266794088538849573/696500000000000000000000000000000 : ℝ)*base77 + (22577388395895150427/696500000000000000000000000000000 : ℝ)*base80 + (8316219211071/3482500000000000000000000000 : ℝ)*base81 + (1282787/250000000000000000000 : ℝ)*base89 + (1282787/250000000000000000000 : ℝ)*base91 + (1282787/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59207/100000 : ℝ) ≤ (206196618993618218678259530506989/348250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9437241/100000000000000 : ℝ)*(upper3) + (43219669/100000000000000 : ℝ)*(upper4) + (6232257/12500000000000 : ℝ)*(lower5) + (1939828861091861/50000000000000 : ℝ)*(major0) + (1939828861091861/50000000000000 : ℝ)*(major1) + (1939828861091861/50000000000000 : ℝ)*(major2) + (5102125489423153/100000000000000 : ℝ)*(sp0) + (1275531360190263/25000000000000 : ℝ)*(sp1) + (5102123782281643/100000000000000 : ℝ)*(sp2) + (527488515777761/20000000000000 : ℝ)*(sp3) + (1716343687/25000000000000 : ℝ)*(sp5) + (8523854157/100000000000000 : ℝ)*(sp6) + (410382777/10000000000000 : ℝ)*(sp7) + (6816712647/100000000000000 : ℝ)*(sp8) + (82420208834893/3125000000000 : ℝ)*(f.failure) + (25510661530679/500000000000 : ℝ)*(f.sum) + (8737211237917/6965000000000000000000000000 : ℝ)*base66 + (1947704817325435663/696500000000000000000000000000000 : ℝ)*base68 + (1200592701067935663/696500000000000000000000000000000 : ℝ)*base70 + (1544969690892564337/696500000000000000000000000000000 : ℝ)*base71 + (48856586574727/6965000000000000000000000000 : ℝ)*base74 + (2280988263003064337/696500000000000000000000000000000 : ℝ)*base75 + (5323076212186564337/696500000000000000000000000000000 : ℝ)*base77 + (2634890351448564337/696500000000000000000000000000000 : ℝ)*base79 + (10746407790289/3482500000000000000000000000 : ℝ)*base81 + (2991893/312500000000000000000 : ℝ)*base89 + (2991893/312500000000000000000 : ℝ)*base91 + (2991893/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (39713/50000 : ℝ) ≤ (138305140066682296103529311248347/174125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6673603/100000000000000 : ℝ)*(upper1) + (32637/250000000000 : ℝ)*(lower3) + (144684139/50000000000000 : ℝ)*(upper4) + (4346077/100000000000000 : ℝ)*(lower5) + (1086989108511599/25000000000000 : ℝ)*(major0) + (1086989108511599/25000000000000 : ℝ)*(major1) + (1086989108511599/25000000000000 : ℝ)*(major2) + (1629293389/50000000000000 : ℝ)*(sp0) + (138396890407/50000000000000 : ℝ)*(sp2) + (47360418993/25000000000000 : ℝ)*(sp3) + (1428407640624341/25000000000000 : ℝ)*(sp8) + (2856816910542071/50000000000000 : ℝ)*(sp9) + (178542407103229/3125000000000 : ℝ)*(sp10) + (18472583675269/625000000000 : ℝ)*(sp11) + (738950707429753/25000000000000 : ℝ)*(f.failure) + (2856816910542071/50000000000000 : ℝ)*(f.sum) + (12974487319797/3482500000000000000000000000 : ℝ)*base65 + (3802583535329383517/348250000000000000000000000000000 : ℝ)*base68 + (3725479279600883517/348250000000000000000000000000000 : ℝ)*base70 + (4737386291541883517/348250000000000000000000000000000 : ℝ)*base72 + (2083756689549/435312500000000000000000000 : ℝ)*base73 + (4108654030937883517/348250000000000000000000000000000 : ℝ)*base76 + (6410720098742883517/348250000000000000000000000000000 : ℝ)*base78 + (5201708387776383517/348250000000000000000000000000000 : ℝ)*base80 + (57273169133443/3482500000000000000000000000 : ℝ)*base82 + (43976753/2500000000000000000000 : ℝ)*base89 + (43976753/2500000000000000000000 : ℝ)*base91 + (43976753/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82847/100000 : ℝ) ≤ (-288505075101380247300211226088633/348250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2924923/12500000000000 : ℝ)*(lower0) + (38836837/100000000000000 : ℝ)*(lower1) + (2493897/10000000000000 : ℝ)*(lower2) + (4829917/100000000000000 : ℝ)*(lower4) + (2191108387745183/50000000000000 : ℝ)*(major0) + (2191108387745183/50000000000000 : ℝ)*(major1) + (2191108387745183/50000000000000 : ℝ)*(major2) + (1155069979/50000000000000 : ℝ)*(sp0) + (49230167037/25000000000000 : ℝ)*(sp5) + (5917707129/4000000000000 : ℝ)*(sp6) + (2906476244832979/50000000000000 : ℝ)*(sp12) + (5812757879137769/100000000000000 : ℝ)*(sp13) + (5812806857127691/100000000000000 : ℝ)*(sp14) + (37238668734147/1250000000000 : ℝ)*(sp15) + (37238668734147/1250000000000 : ℝ)*(f.failure) + (5812954799805917/100000000000000 : ℝ)*(f.sum) + (351462030286141/6965000000000000000000000000 : ℝ)*base66 + (345080955813396211/696500000000000000000000000000000 : ℝ)*base67 + (1243163675187603789/696500000000000000000000000000000 : ℝ)*base70 + (26056240442248896211/696500000000000000000000000000000 : ℝ)*base71 + (24432641890921/6965000000000000000000000000 : ℝ)*base74 + (3631741590427396211/696500000000000000000000000000000 : ℝ)*base75 + (38695207640033603789/696500000000000000000000000000000 : ℝ)*base78 + (3784531534065896211/696500000000000000000000000000000 : ℝ)*base79 + (597432500417/217656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (787147/125000000000000000000 : ℝ)*base89 + (787147/125000000000000000000 : ℝ)*base91 + (787147/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1020_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147099001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13973/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59207/100000 : ℝ) else (39713/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82847/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1020_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2053/512 : ℝ) ≤ p) (hpb : p ≤ (8213/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147099001/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13973/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59207/100000 : ℝ) else (39713/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82847/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1020_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
