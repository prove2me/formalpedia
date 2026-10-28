-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:39:11.658768+00:00
-- url     : https://prove2.me/submissions/cb015805-b4d5-4744-a0ea-3df7e613ec90

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
theorem support_rectangle_w1030_box_0 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045445001/5000000000 : ℝ)*x 0 + (5377852901/10000000000 : ℝ)*x 1 + (215114119/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045445001/5000000000 : ℝ)^8223 ≤ (12442632727523/100000000000000 : ℝ)^6175 := by
    have hnat : (1045445001 : ℕ)^8223*100000000000000^6175 ≤ 12442632727523^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045445001 5000000000 12442632727523 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377852901/10000000000 : ℝ)^8223 ≤ (43778683229341/100000000000000 : ℝ)^6175 := by
    have hnat : (5377852901 : ℕ)^8223*100000000000000^6175 ≤ 43778683229341^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377852901 10000000000 43778683229341 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215114119/400000000 : ℝ)^8223 ≤ (21889342015767/50000000000000 : ℝ)^6175 := by
    have hnat : (215114119 : ℕ)^8223*50000000000000^6175 ≤ 21889342015767^6175*400000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215114119 400000000 21889342015767 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045445001/5000000000 : ℝ), (5377852901/10000000000 : ℝ), (215114119/400000000 : ℝ)] ![(12442632727523/100000000000000 : ℝ), (43778683229341/100000000000000 : ℝ), (21889342015767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045445001/5000000000 : ℝ)|^8223 ≤ (12442632727523/100000000000000 : ℝ)^6175
        have hw : |(-1045445001/5000000000 : ℝ)|=(1045445001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377852901/10000000000 : ℝ)|^8223 ≤ (43778683229341/100000000000000 : ℝ)^6175
        have hw : |(5377852901/10000000000 : ℝ)|=(5377852901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215114119/400000000 : ℝ)|^8223 ≤ (21889342015767/50000000000000 : ℝ)^6175
        have hw : |(215114119/400000000 : ℝ)|=(215114119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_1 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294777159/10000000000 : ℝ)*x 0 + (-1101626511/5000000000 : ℝ)*x 1 + (5377852497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294777159/10000000000 : ℝ)^8223 ≤ (4288042023203/10000000000000 : ℝ)^6175 := by
    have hnat : (5294777159 : ℕ)^8223*10000000000000^6175 ≤ 4288042023203^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294777159 10000000000 4288042023203 10000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101626511/5000000000 : ℝ)^8223 ≤ (13340900899713/100000000000000 : ℝ)^6175 := by
    have hnat : (1101626511 : ℕ)^8223*100000000000000^6175 ≤ 13340900899713^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101626511 5000000000 13340900899713 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377852497/10000000000 : ℝ)^8223 ≤ (43778678849801/100000000000000 : ℝ)^6175 := by
    have hnat : (5377852497 : ℕ)^8223*100000000000000^6175 ≤ 43778678849801^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377852497 10000000000 43778678849801 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294777159/10000000000 : ℝ), (-1101626511/5000000000 : ℝ), (5377852497/10000000000 : ℝ)] ![(4288042023203/10000000000000 : ℝ), (13340900899713/100000000000000 : ℝ), (43778678849801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294777159/10000000000 : ℝ)|^8223 ≤ (4288042023203/10000000000000 : ℝ)^6175
        have hw : |(5294777159/10000000000 : ℝ)|=(5294777159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101626511/5000000000 : ℝ)|^8223 ≤ (13340900899713/100000000000000 : ℝ)^6175
        have hw : |(-1101626511/5000000000 : ℝ)|=(1101626511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377852497/10000000000 : ℝ)|^8223 ≤ (43778678849801/100000000000000 : ℝ)^6175
        have hw : |(5377852497/10000000000 : ℝ)|=(5377852497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_2 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294777421/10000000000 : ℝ)*x 0 + (215114093/400000000 : ℝ)*x 1 + (-2203252903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294777421/10000000000 : ℝ)^8223 ≤ (42880423057599/100000000000000 : ℝ)^6175 := by
    have hnat : (5294777421 : ℕ)^8223*100000000000000^6175 ≤ 42880423057599^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294777421 10000000000 42880423057599 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215114093/400000000 : ℝ)^8223 ≤ (8755735397049/20000000000000 : ℝ)^6175 := by
    have hnat : (215114093 : ℕ)^8223*20000000000000^6175 ≤ 8755735397049^6175*400000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215114093 400000000 8755735397049 20000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203252903/10000000000 : ℝ)^8223 ≤ (13340899940177/100000000000000 : ℝ)^6175 := by
    have hnat : (2203252903 : ℕ)^8223*100000000000000^6175 ≤ 13340899940177^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203252903 10000000000 13340899940177 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294777421/10000000000 : ℝ), (215114093/400000000 : ℝ), (-2203252903/10000000000 : ℝ)] ![(42880423057599/100000000000000 : ℝ), (8755735397049/20000000000000 : ℝ), (13340899940177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294777421/10000000000 : ℝ)|^8223 ≤ (42880423057599/100000000000000 : ℝ)^6175
        have hw : |(5294777421/10000000000 : ℝ)|=(5294777421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215114093/400000000 : ℝ)|^8223 ≤ (8755735397049/20000000000000 : ℝ)^6175
        have hw : |(215114093/400000000 : ℝ)|=(215114093/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203252903/10000000000 : ℝ)|^8223 ≤ (13340899940177/100000000000000 : ℝ)^6175
        have hw : |(-2203252903/10000000000 : ℝ)|=(2203252903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_3 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4489511421/10000000000 : ℝ)*x 0 + (4328477929/10000000000 : ℝ)*x 1 + (865695703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489511421/10000000000 : ℝ)^8223 ≤ (1721145003057/5000000000000 : ℝ)^6175 := by
    have hnat : (4489511421 : ℕ)^8223*5000000000000^6175 ≤ 1721145003057^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489511421 10000000000 1721145003057 5000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4328477929/10000000000 : ℝ)^8223 ≤ (3278854700373/10000000000000 : ℝ)^6175 := by
    have hnat : (4328477929 : ℕ)^8223*10000000000000^6175 ≤ 3278854700373^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328477929 10000000000 3278854700373 10000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865695703/2000000000 : ℝ)^8223 ≤ (32788552914961/100000000000000 : ℝ)^6175 := by
    have hnat : (865695703 : ℕ)^8223*100000000000000^6175 ≤ 32788552914961^6175*2000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865695703 2000000000 32788552914961 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489511421/10000000000 : ℝ), (4328477929/10000000000 : ℝ), (865695703/2000000000 : ℝ)] ![(1721145003057/5000000000000 : ℝ), (3278854700373/10000000000000 : ℝ), (32788552914961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489511421/10000000000 : ℝ)|^8223 ≤ (1721145003057/5000000000000 : ℝ)^6175
        have hw : |(4489511421/10000000000 : ℝ)|=(4489511421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4328477929/10000000000 : ℝ)|^8223 ≤ (3278854700373/10000000000000 : ℝ)^6175
        have hw : |(4328477929/10000000000 : ℝ)|=(4328477929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865695703/2000000000 : ℝ)|^8223 ≤ (32788552914961/100000000000000 : ℝ)^6175
        have hw : |(865695703/2000000000 : ℝ)|=(865695703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_4 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-470747853/2000000000 : ℝ)*x 0 + (5279530317/10000000000 : ℝ)*x 1 + (2639765363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470747853/2000000000 : ℝ)^8223 ≤ (14567860641507/100000000000000 : ℝ)^6175 := by
    have hnat : (470747853 : ℕ)^8223*100000000000000^6175 ≤ 14567860641507^6175*2000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470747853 2000000000 14567860641507 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279530317/10000000000 : ℝ)^8223 ≤ (42716067470597/100000000000000 : ℝ)^6175 := by
    have hnat : (5279530317 : ℕ)^8223*100000000000000^6175 ≤ 42716067470597^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279530317 10000000000 42716067470597 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639765363/5000000000 : ℝ)^8223 ≤ (5339508984661/12500000000000 : ℝ)^6175 := by
    have hnat : (2639765363 : ℕ)^8223*12500000000000^6175 ≤ 5339508984661^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639765363 5000000000 5339508984661 12500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470747853/2000000000 : ℝ), (5279530317/10000000000 : ℝ), (2639765363/5000000000 : ℝ)] ![(14567860641507/100000000000000 : ℝ), (42716067470597/100000000000000 : ℝ), (5339508984661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470747853/2000000000 : ℝ)|^8223 ≤ (14567860641507/100000000000000 : ℝ)^6175
        have hw : |(-470747853/2000000000 : ℝ)|=(470747853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279530317/10000000000 : ℝ)|^8223 ≤ (42716067470597/100000000000000 : ℝ)^6175
        have hw : |(5279530317/10000000000 : ℝ)|=(5279530317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639765363/5000000000 : ℝ)|^8223 ≤ (5339508984661/12500000000000 : ℝ)^6175
        have hw : |(2639765363/5000000000 : ℝ)|=(2639765363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_5 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364419239/10000000000 : ℝ)*x 0 + (-560394561/2500000000 : ℝ)*x 1 + (5279530153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364419239/10000000000 : ℝ)^8223 ≤ (5454139589367/12500000000000 : ℝ)^6175 := by
    have hnat : (5364419239 : ℕ)^8223*12500000000000^6175 ≤ 5454139589367^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364419239 10000000000 5454139589367 12500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560394561/2500000000 : ℝ)^8223 ≤ (3412704393149/25000000000000 : ℝ)^6175 := by
    have hnat : (560394561 : ℕ)^8223*25000000000000^6175 ≤ 3412704393149^6175*2500000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560394561 2500000000 3412704393149 25000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279530153/10000000000 : ℝ)^8223 ≤ (42716065703611/100000000000000 : ℝ)^6175 := by
    have hnat : (5279530153 : ℕ)^8223*100000000000000^6175 ≤ 42716065703611^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279530153 10000000000 42716065703611 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364419239/10000000000 : ℝ), (-560394561/2500000000 : ℝ), (5279530153/10000000000 : ℝ)] ![(5454139589367/12500000000000 : ℝ), (3412704393149/25000000000000 : ℝ), (42716065703611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364419239/10000000000 : ℝ)|^8223 ≤ (5454139589367/12500000000000 : ℝ)^6175
        have hw : |(5364419239/10000000000 : ℝ)|=(5364419239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560394561/2500000000 : ℝ)|^8223 ≤ (3412704393149/25000000000000 : ℝ)^6175
        have hw : |(-560394561/2500000000 : ℝ)|=(560394561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279530153/10000000000 : ℝ)|^8223 ≤ (42716065703611/100000000000000 : ℝ)^6175
        have hw : |(5279530153/10000000000 : ℝ)|=(5279530153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_6 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072883753/2000000000 : ℝ)*x 0 + (2639765397/5000000000 : ℝ)*x 1 + (-1120789013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072883753/2000000000 : ℝ)^8223 ≤ (21816555790413/50000000000000 : ℝ)^6175 := by
    have hnat : (1072883753 : ℕ)^8223*50000000000000^6175 ≤ 21816555790413^6175*2000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072883753 2000000000 21816555790413 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639765397/5000000000 : ℝ)^8223 ≤ (42716072609941/100000000000000 : ℝ)^6175 := by
    have hnat : (2639765397 : ℕ)^8223*100000000000000^6175 ≤ 42716072609941^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639765397 5000000000 42716072609941 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120789013/5000000000 : ℝ)^8223 ≤ (13650815804709/100000000000000 : ℝ)^6175 := by
    have hnat : (1120789013 : ℕ)^8223*100000000000000^6175 ≤ 13650815804709^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120789013 5000000000 13650815804709 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072883753/2000000000 : ℝ), (2639765397/5000000000 : ℝ), (-1120789013/5000000000 : ℝ)] ![(21816555790413/50000000000000 : ℝ), (42716072609941/100000000000000 : ℝ), (13650815804709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072883753/2000000000 : ℝ)|^8223 ≤ (21816555790413/50000000000000 : ℝ)^6175
        have hw : |(1072883753/2000000000 : ℝ)|=(1072883753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639765397/5000000000 : ℝ)|^8223 ≤ (42716072609941/100000000000000 : ℝ)^6175
        have hw : |(2639765397/5000000000 : ℝ)|=(2639765397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120789013/5000000000 : ℝ)|^8223 ≤ (13650815804709/100000000000000 : ℝ)^6175
        have hw : |(-1120789013/5000000000 : ℝ)|=(1120789013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_7 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (533945961/1250000000 : ℝ)*x 0 + (4437428011/10000000000 : ℝ)*x 1 + (2218714307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533945961/1250000000 : ℝ)^8223 ≤ (2013482787767/6250000000000 : ℝ)^6175 := by
    have hnat : (533945961 : ℕ)^8223*6250000000000^6175 ≤ 2013482787767^6175*1250000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533945961 1250000000 2013482787767 6250000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4437428011/10000000000 : ℝ)^8223 ≤ (4236516828183/12500000000000 : ℝ)^6175 := by
    have hnat : (4437428011 : ℕ)^8223*12500000000000^6175 ≤ 4236516828183^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437428011 10000000000 4236516828183 12500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218714307/5000000000 : ℝ)^8223 ≤ (33892140758539/100000000000000 : ℝ)^6175 := by
    have hnat : (2218714307 : ℕ)^8223*100000000000000^6175 ≤ 33892140758539^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218714307 5000000000 33892140758539 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533945961/1250000000 : ℝ), (4437428011/10000000000 : ℝ), (2218714307/5000000000 : ℝ)] ![(2013482787767/6250000000000 : ℝ), (4236516828183/12500000000000 : ℝ), (33892140758539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533945961/1250000000 : ℝ)|^8223 ≤ (2013482787767/6250000000000 : ℝ)^6175
        have hw : |(533945961/1250000000 : ℝ)|=(533945961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4437428011/10000000000 : ℝ)|^8223 ≤ (4236516828183/12500000000000 : ℝ)^6175
        have hw : |(4437428011/10000000000 : ℝ)|=(4437428011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2218714307/5000000000 : ℝ)|^8223 ≤ (33892140758539/100000000000000 : ℝ)^6175
        have hw : |(2218714307/5000000000 : ℝ)|=(2218714307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_8 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2298913843/10000000000 : ℝ)*x 0 + (260644237/500000000 : ℝ)*x 1 + (1077489781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2298913843/10000000000 : ℝ)^8223 ≤ (14117746008423/100000000000000 : ℝ)^6175 := by
    have hnat : (2298913843 : ℕ)^8223*100000000000000^6175 ≤ 14117746008423^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298913843 10000000000 14117746008423 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260644237/500000000 : ℝ)^8223 ≤ (41999515023703/100000000000000 : ℝ)^6175 := by
    have hnat : (260644237 : ℕ)^8223*100000000000000^6175 ≤ 41999515023703^6175*500000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260644237 500000000 41999515023703 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077489781/2000000000 : ℝ)^8223 ≤ (4388273895017/10000000000000 : ℝ)^6175 := by
    have hnat : (1077489781 : ℕ)^8223*10000000000000^6175 ≤ 4388273895017^6175*2000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077489781 2000000000 4388273895017 10000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2298913843/10000000000 : ℝ), (260644237/500000000 : ℝ), (1077489781/2000000000 : ℝ)] ![(14117746008423/100000000000000 : ℝ), (41999515023703/100000000000000 : ℝ), (4388273895017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2298913843/10000000000 : ℝ)|^8223 ≤ (14117746008423/100000000000000 : ℝ)^6175
        have hw : |(-2298913843/10000000000 : ℝ)|=(2298913843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260644237/500000000 : ℝ)|^8223 ≤ (41999515023703/100000000000000 : ℝ)^6175
        have hw : |(260644237/500000000 : ℝ)|=(260644237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077489781/2000000000 : ℝ)|^8223 ≤ (4388273895017/10000000000000 : ℝ)^6175
        have hw : |(1077489781/2000000000 : ℝ)|=(1077489781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_9 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287975837/10000000000 : ℝ)*x 0 + (-2199441563/10000000000 : ℝ)*x 1 + (1346862183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287975837/10000000000 : ℝ)^8223 ≤ (42807086216927/100000000000000 : ℝ)^6175 := by
    have hnat : (5287975837 : ℕ)^8223*100000000000000^6175 ≤ 42807086216927^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287975837 10000000000 42807086216927 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199441563/10000000000 : ℝ)^8223 ≤ (3327544172673/25000000000000 : ℝ)^6175 := by
    have hnat : (2199441563 : ℕ)^8223*25000000000000^6175 ≤ 3327544172673^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199441563 10000000000 3327544172673 25000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346862183/2500000000 : ℝ)^8223 ≤ (85708470847/195312500000 : ℝ)^6175 := by
    have hnat : (1346862183 : ℕ)^8223*195312500000^6175 ≤ 85708470847^6175*2500000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346862183 2500000000 85708470847 195312500000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287975837/10000000000 : ℝ), (-2199441563/10000000000 : ℝ), (1346862183/2500000000 : ℝ)] ![(42807086216927/100000000000000 : ℝ), (3327544172673/25000000000000 : ℝ), (85708470847/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287975837/10000000000 : ℝ)|^8223 ≤ (42807086216927/100000000000000 : ℝ)^6175
        have hw : |(5287975837/10000000000 : ℝ)|=(5287975837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199441563/10000000000 : ℝ)|^8223 ≤ (3327544172673/25000000000000 : ℝ)^6175
        have hw : |(-2199441563/10000000000 : ℝ)|=(2199441563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346862183/2500000000 : ℝ)|^8223 ≤ (85708470847/195312500000 : ℝ)^6175
        have hw : |(1346862183/2500000000 : ℝ)|=(1346862183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_10 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287976179/10000000000 : ℝ)*x 0 + (5387448893/10000000000 : ℝ)*x 1 + (-219944089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287976179/10000000000 : ℝ)^8223 ≤ (21403544951847/50000000000000 : ℝ)^6175 := by
    have hnat : (5287976179 : ℕ)^8223*50000000000000^6175 ≤ 21403544951847^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287976179 10000000000 21403544951847 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387448893/10000000000 : ℝ)^8223 ≤ (5485342352501/12500000000000 : ℝ)^6175 := by
    have hnat : (5387448893 : ℕ)^8223*12500000000000^6175 ≤ 5485342352501^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387448893 10000000000 5485342352501 12500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219944089/1000000000 : ℝ)^8223 ≤ (1331017126719/10000000000000 : ℝ)^6175 := by
    have hnat : (219944089 : ℕ)^8223*10000000000000^6175 ≤ 1331017126719^6175*1000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219944089 1000000000 1331017126719 10000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287976179/10000000000 : ℝ), (5387448893/10000000000 : ℝ), (-219944089/1000000000 : ℝ)] ![(21403544951847/50000000000000 : ℝ), (5485342352501/12500000000000 : ℝ), (1331017126719/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287976179/10000000000 : ℝ)|^8223 ≤ (21403544951847/50000000000000 : ℝ)^6175
        have hw : |(5287976179/10000000000 : ℝ)|=(5287976179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387448893/10000000000 : ℝ)|^8223 ≤ (5485342352501/12500000000000 : ℝ)^6175
        have hw : |(5387448893/10000000000 : ℝ)|=(5387448893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219944089/1000000000 : ℝ)|^8223 ≤ (1331017126719/10000000000000 : ℝ)^6175
        have hw : |(-219944089/1000000000 : ℝ)|=(219944089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_11 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2255254423/5000000000 : ℝ)*x 0 + (539729881/1250000000 : ℝ)*x 1 + (4317838899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255254423/5000000000 : ℝ)^8223 ≤ (17318728877959/50000000000000 : ℝ)^6175 := by
    have hnat : (2255254423 : ℕ)^8223*50000000000000^6175 ≤ 17318728877959^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255254423 5000000000 17318728877959 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539729881/1250000000 : ℝ)^8223 ≤ (16340635931061/50000000000000 : ℝ)^6175 := by
    have hnat : (539729881 : ℕ)^8223*50000000000000^6175 ≤ 16340635931061^6175*1250000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539729881 1250000000 16340635931061 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317838899/10000000000 : ℝ)^8223 ≤ (32681270360323/100000000000000 : ℝ)^6175 := by
    have hnat : (4317838899 : ℕ)^8223*100000000000000^6175 ≤ 32681270360323^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317838899 10000000000 32681270360323 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2255254423/5000000000 : ℝ), (539729881/1250000000 : ℝ), (4317838899/10000000000 : ℝ)] ![(17318728877959/50000000000000 : ℝ), (16340635931061/50000000000000 : ℝ), (32681270360323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2255254423/5000000000 : ℝ)|^8223 ≤ (17318728877959/50000000000000 : ℝ)^6175
        have hw : |(2255254423/5000000000 : ℝ)|=(2255254423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539729881/1250000000 : ℝ)|^8223 ≤ (16340635931061/50000000000000 : ℝ)^6175
        have hw : |(539729881/1250000000 : ℝ)|=(539729881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317838899/10000000000 : ℝ)|^8223 ≤ (32681270360323/100000000000000 : ℝ)^6175
        have hw : |(4317838899/10000000000 : ℝ)|=(4317838899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_12 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429221741/2000000000 : ℝ)*x 0 + (2721567019/5000000000 : ℝ)*x 1 + (5271549229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429221741/2000000000 : ℝ)^8223 ≤ (12882121127971/100000000000000 : ℝ)^6175 := by
    have hnat : (429221741 : ℕ)^8223*100000000000000^6175 ≤ 12882121127971^6175*2000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429221741 2000000000 12882121127971 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721567019/5000000000 : ℝ)^8223 ≤ (8897556101573/20000000000000 : ℝ)^6175 := by
    have hnat : (2721567019 : ℕ)^8223*20000000000000^6175 ≤ 8897556101573^6175*5000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721567019 5000000000 8897556101573 20000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271549229/10000000000 : ℝ)^8223 ≤ (1065752458763/2500000000000 : ℝ)^6175 := by
    have hnat : (5271549229 : ℕ)^8223*2500000000000^6175 ≤ 1065752458763^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271549229 10000000000 1065752458763 2500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429221741/2000000000 : ℝ), (2721567019/5000000000 : ℝ), (5271549229/10000000000 : ℝ)] ![(12882121127971/100000000000000 : ℝ), (8897556101573/20000000000000 : ℝ), (1065752458763/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429221741/2000000000 : ℝ)|^8223 ≤ (12882121127971/100000000000000 : ℝ)^6175
        have hw : |(-429221741/2000000000 : ℝ)|=(429221741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721567019/5000000000 : ℝ)|^8223 ≤ (8897556101573/20000000000000 : ℝ)^6175
        have hw : |(2721567019/5000000000 : ℝ)|=(2721567019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271549229/10000000000 : ℝ)|^8223 ≤ (1065752458763/2500000000000 : ℝ)^6175
        have hw : |(5271549229/10000000000 : ℝ)|=(5271549229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_13 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370070667/10000000000 : ℝ)*x 0 + (-438404/1953125 : ℝ)*x 1 + (329471837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370070667/10000000000 : ℝ)^8223 ≤ (1092358515051/2500000000000 : ℝ)^6175 := by
    have hnat : (5370070667 : ℕ)^8223*2500000000000^6175 ≤ 1092358515051^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370070667 10000000000 1092358515051 2500000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438404/1953125 : ℝ)^8223 ≤ (213680613593/1562500000000 : ℝ)^6175 := by
    have hnat : (438404 : ℕ)^8223*1562500000000^6175 ≤ 213680613593^6175*1953125^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438404 1953125 213680613593 1562500000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329471837/625000000 : ℝ)^8223 ≤ (42630100105851/100000000000000 : ℝ)^6175 := by
    have hnat : (329471837 : ℕ)^8223*100000000000000^6175 ≤ 42630100105851^6175*625000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329471837 625000000 42630100105851 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370070667/10000000000 : ℝ), (-438404/1953125 : ℝ), (329471837/625000000 : ℝ)] ![(1092358515051/2500000000000 : ℝ), (213680613593/1562500000000 : ℝ), (42630100105851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370070667/10000000000 : ℝ)|^8223 ≤ (1092358515051/2500000000000 : ℝ)^6175
        have hw : |(5370070667/10000000000 : ℝ)|=(5370070667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438404/1953125 : ℝ)|^8223 ≤ (213680613593/1562500000000 : ℝ)^6175
        have hw : |(-438404/1953125 : ℝ)|=(438404/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329471837/625000000 : ℝ)|^8223 ≤ (42630100105851/100000000000000 : ℝ)^6175
        have hw : |(329471837/625000000 : ℝ)|=(329471837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_14 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370070033/10000000000 : ℝ)*x 0 + (5271548979/10000000000 : ℝ)*x 1 + (-17957039/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370070033/10000000000 : ℝ)^8223 ≤ (21847166866249/50000000000000 : ℝ)^6175 := by
    have hnat : (5370070033 : ℕ)^8223*50000000000000^6175 ≤ 21847166866249^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370070033 10000000000 21847166866249 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271548979/10000000000 : ℝ)^8223 ≤ (8526019131659/20000000000000 : ℝ)^6175 := by
    have hnat : (5271548979 : ℕ)^8223*20000000000000^6175 ≤ 8526019131659^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271548979 10000000000 8526019131659 20000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17957039/80000000 : ℝ)^8223 ≤ (13675570587913/100000000000000 : ℝ)^6175 := by
    have hnat : (17957039 : ℕ)^8223*100000000000000^6175 ≤ 13675570587913^6175*80000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17957039 80000000 13675570587913 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370070033/10000000000 : ℝ), (5271548979/10000000000 : ℝ), (-17957039/80000000 : ℝ)] ![(21847166866249/50000000000000 : ℝ), (8526019131659/20000000000000 : ℝ), (13675570587913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370070033/10000000000 : ℝ)|^8223 ≤ (21847166866249/50000000000000 : ℝ)^6175
        have hw : |(5370070033/10000000000 : ℝ)|=(5370070033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271548979/10000000000 : ℝ)|^8223 ≤ (8526019131659/20000000000000 : ℝ)^6175
        have hw : |(5271548979/10000000000 : ℝ)|=(5271548979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17957039/80000000 : ℝ)|^8223 ≤ (13675570587913/100000000000000 : ℝ)^6175
        have hw : |(-17957039/80000000 : ℝ)|=(17957039/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1030_box_15 (p : ℝ) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4253646069/10000000000 : ℝ)*x 0 + (1111567023/2500000000 : ℝ)*x 1 + (4446266987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253646069/10000000000 : ℝ)^8223 ≤ (16017929394291/50000000000000 : ℝ)^6175 := by
    have hnat : (4253646069 : ℕ)^8223*50000000000000^6175 ≤ 16017929394291^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253646069 10000000000 16017929394291 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111567023/2500000000 : ℝ)^8223 ≤ (33982076215591/100000000000000 : ℝ)^6175 := by
    have hnat : (1111567023 : ℕ)^8223*100000000000000^6175 ≤ 33982076215591^6175*2500000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111567023 2500000000 33982076215591 100000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4446266987/10000000000 : ℝ)^8223 ≤ (16991032484643/50000000000000 : ℝ)^6175 := by
    have hnat : (4446266987 : ℕ)^8223*50000000000000^6175 ≤ 16991032484643^6175*10000000000^8223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446266987 10000000000 16991032484643 50000000000000 8223 6175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8223/2048 : ℝ)) 8223 6175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253646069/10000000000 : ℝ), (1111567023/2500000000 : ℝ), (4446266987/10000000000 : ℝ)] ![(16017929394291/50000000000000 : ℝ), (33982076215591/100000000000000 : ℝ), (16991032484643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253646069/10000000000 : ℝ)|^8223 ≤ (16017929394291/50000000000000 : ℝ)^6175
        have hw : |(4253646069/10000000000 : ℝ)|=(4253646069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111567023/2500000000 : ℝ)|^8223 ≤ (33982076215591/100000000000000 : ℝ)^6175
        have hw : |(1111567023/2500000000 : ℝ)|=(1111567023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4446266987/10000000000 : ℝ)|^8223 ≤ (16991032484643/50000000000000 : ℝ)^6175
        have hw : |(4446266987/10000000000 : ℝ)|=(4446266987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1030_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4602913/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29607/50000 : ℝ) ∧ (39729/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8287/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (699/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (699/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (699/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (699/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (699/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (699/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11201/100000 : ℝ) ^ (4111/1024 : ℝ) ≤ (3048809452218443/20000000000000000000 : ℝ) := by
    have hpowers : (11201/100000 : ℝ)^4111 ≤ (3048809452218443/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11201 : ℕ)^4111*20000000000000000000^1024 ≤ 3048809452218443^1024*100000^4111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11201 100000 3048809452218443 20000000000000000000 4111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11201/100000 : ℝ)) (X := (3048809452218443/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (699/5000 : ℝ) ^ (4111/1024 : ℝ) ≤ (4638971601036461/12500000000000000000 : ℝ) := by
    have hpowers : (699/5000 : ℝ)^4111 ≤ (4638971601036461/12500000000000000000 : ℝ)^1024 := by
      have hnat : (699 : ℕ)^4111*12500000000000000000^1024 ≤ 4638971601036461^1024*5000^4111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 5000 4638971601036461 12500000000000000000 4111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/5000 : ℝ)) (X := (4638971601036461/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003048809452218443/10000000000000000000 : ℝ) ≤ (10000759334364229/10000000000000000 : ℝ) ^ (4111/1024 : ℝ) := by
    have hpowers : (10003048809452218443/10000000000000000000 : ℝ)^1024 ≤ (10000759334364229/10000000000000000 : ℝ)^4111 := by
      have hnat : (10003048809452218443 : ℕ)^1024*10000000000000000^4111 ≤ 10000759334364229^4111*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003048809452218443 10000000000000000000 10000759334364229 10000000000000000 1024 4111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000759334364229/10000000000000000 : ℝ)) (X := (10003048809452218443/10000000000000000000 : ℝ)) (by norm_num) 4111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052355820069383903/100000000000000000000 : ℝ) ≤ (2500325965849073/2500000000000000 : ℝ) ^ (4111/1024 : ℝ) := by
    have hpowers : (100052355820069383903/100000000000000000000 : ℝ)^1024 ≤ (2500325965849073/2500000000000000 : ℝ)^4111 := by
      have hnat : (100052355820069383903 : ℕ)^1024*2500000000000000^4111 ≤ 2500325965849073^4111*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052355820069383903 100000000000000000000 2500325965849073 2500000000000000 1024 4111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500325965849073/2500000000000000 : ℝ)) (X := (100052355820069383903/100000000000000000000 : ℝ)) (by norm_num) 4111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254638971601036461/6250000000000000000 : ℝ) ≤ (2000369678485671/2000000000000000 : ℝ) ^ (4111/1024 : ℝ) := by
    have hpowers : (6254638971601036461/6250000000000000000 : ℝ)^1024 ≤ (2000369678485671/2000000000000000 : ℝ)^4111 := by
      have hnat : (6254638971601036461 : ℕ)^1024*2000000000000000^4111 ≤ 2000369678485671^4111*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254638971601036461 6250000000000000000 2000369678485671 2000000000000000 1024 4111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000369678485671/2000000000000000 : ℝ)) (X := (6254638971601036461/6250000000000000000 : ℝ)) (by norm_num) 4111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3048809452218443/20000000000000000000 : ℝ) ≤ ((5555982330164383413/5558000000000000000 : ℝ)+2*(544529032063/277900000000000 : ℝ)*(11201/100000 : ℝ))^(4111/1024 : ℝ) := by
    rw [show (5555982330164383413/5558000000000000000 : ℝ)+2*(544529032063/277900000000000 : ℝ)*(11201/100000 : ℝ)=(10000759334364229/10000000000000000 : ℝ) by norm_num, show 1+2*(3048809452218443/20000000000000000000 : ℝ)=(10003048809452218443/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4638971601036461/12500000000000000000 : ℝ)+(3048809452218443/20000000000000000000 : ℝ) ≤ ((5555982330164383413/5558000000000000000 : ℝ)+(544529032063/277900000000000 : ℝ)*((699/5000 : ℝ)+(11201/100000 : ℝ)))^(4111/1024 : ℝ) := by
    rw [show (5555982330164383413/5558000000000000000 : ℝ)+(544529032063/277900000000000 : ℝ)*((699/5000 : ℝ)+(11201/100000 : ℝ))=(2500325965849073/2500000000000000 : ℝ) by norm_num, show 1+(4638971601036461/12500000000000000000 : ℝ)+(3048809452218443/20000000000000000000 : ℝ)=(100052355820069383903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4638971601036461/12500000000000000000 : ℝ) ≤ ((5555982330164383413/5558000000000000000 : ℝ)+2*(544529032063/277900000000000 : ℝ)*(699/5000 : ℝ))^(4111/1024 : ℝ) := by
    rw [show (5555982330164383413/5558000000000000000 : ℝ)+2*(544529032063/277900000000000 : ℝ)*(699/5000 : ℝ)=(2000369678485671/2000000000000000 : ℝ) by norm_num, show 1+2*(4638971601036461/12500000000000000000 : ℝ)=(6254638971601036461/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5555982330164383413/5558000000000000000 : ℝ)*(X 1 0+X 2 0)+(544529032063/277900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4111/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (5555982330164383413/5558000000000000000 : ℝ)) (alpha := (544529032063/277900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5555982330164383413/5558000000000000000 : ℝ)*(X 0 1+X 2 1)+(544529032063/277900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4111/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (5555982330164383413/5558000000000000000 : ℝ)) (alpha := (544529032063/277900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5555982330164383413/5558000000000000000 : ℝ)*(X 0 2+X 1 2)+(544529032063/277900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4111/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (5555982330164383413/5558000000000000000 : ℝ)) (alpha := (544529032063/277900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045445001/5000000000 : ℝ)*X 0 0+(5377852901/10000000000 : ℝ)*X 0 1+(215114119/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294777159/10000000000 : ℝ)*X 1 0+(-1101626511/5000000000 : ℝ)*X 1 1+(5377852497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294777421/10000000000 : ℝ)*X 2 0+(215114093/400000000 : ℝ)*X 2 1+(-2203252903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4489511421/10000000000 : ℝ)*X 0 0+(4328477929/10000000000 : ℝ)*X 0 1+(865695703/2000000000 : ℝ)*X 0 2+(4489511421/10000000000 : ℝ)*X 1 0+(4328477929/10000000000 : ℝ)*X 1 1+(865695703/2000000000 : ℝ)*X 1 2+(4489511421/10000000000 : ℝ)*X 2 0+(4328477929/10000000000 : ℝ)*X 2 1+(865695703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-470747853/2000000000 : ℝ)*X 0 0+(5279530317/10000000000 : ℝ)*X 0 1+(2639765363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364419239/10000000000 : ℝ)*X 1 0+(-560394561/2500000000 : ℝ)*X 1 1+(5279530153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072883753/2000000000 : ℝ)*X 2 0+(2639765397/5000000000 : ℝ)*X 2 1+(-1120789013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533945961/1250000000 : ℝ)*X 0 0+(4437428011/10000000000 : ℝ)*X 0 1+(2218714307/5000000000 : ℝ)*X 0 2+(533945961/1250000000 : ℝ)*X 1 0+(4437428011/10000000000 : ℝ)*X 1 1+(2218714307/5000000000 : ℝ)*X 1 2+(533945961/1250000000 : ℝ)*X 2 0+(4437428011/10000000000 : ℝ)*X 2 1+(2218714307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2298913843/10000000000 : ℝ)*X 0 0+(260644237/500000000 : ℝ)*X 0 1+(1077489781/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287975837/10000000000 : ℝ)*X 1 0+(-2199441563/10000000000 : ℝ)*X 1 1+(1346862183/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287976179/10000000000 : ℝ)*X 2 0+(5387448893/10000000000 : ℝ)*X 2 1+(-219944089/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2255254423/5000000000 : ℝ)*X 0 0+(539729881/1250000000 : ℝ)*X 0 1+(4317838899/10000000000 : ℝ)*X 0 2+(2255254423/5000000000 : ℝ)*X 1 0+(539729881/1250000000 : ℝ)*X 1 1+(4317838899/10000000000 : ℝ)*X 1 2+(2255254423/5000000000 : ℝ)*X 2 0+(539729881/1250000000 : ℝ)*X 2 1+(4317838899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-429221741/2000000000 : ℝ)*X 0 0+(2721567019/5000000000 : ℝ)*X 0 1+(5271549229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370070667/10000000000 : ℝ)*X 1 0+(-438404/1953125 : ℝ)*X 1 1+(329471837/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370070033/10000000000 : ℝ)*X 2 0+(5271548979/10000000000 : ℝ)*X 2 1+(-17957039/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4253646069/10000000000 : ℝ)*X 0 0+(1111567023/2500000000 : ℝ)*X 0 1+(4446266987/10000000000 : ℝ)*X 0 2+(4253646069/10000000000 : ℝ)*X 1 0+(1111567023/2500000000 : ℝ)*X 1 1+(4446266987/10000000000 : ℝ)*X 1 2+(4253646069/10000000000 : ℝ)*X 2 0+(1111567023/2500000000 : ℝ)*X 2 1+(4446266987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1030_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-86455736146728442890461114094567/138950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106526493/100000000000000 : ℝ)*(upper1) + (1954527/1562500000000 : ℝ)*(upper2) + (27227953/50000000000000 : ℝ)*(lower4) + (34020911/10000000000000 : ℝ)*(upper5) + (1912872972347847/50000000000000 : ℝ)*(major0) + (1912872972347847/50000000000000 : ℝ)*(major1) + (1912872972347847/50000000000000 : ℝ)*(major2) + (18740730679/100000000000000 : ℝ)*(sp1) + (99813397/1000000000000 : ℝ)*(sp2) + (1074417523/6250000000000 : ℝ)*(sp3) + (634358095098941/12500000000000 : ℝ)*(sp4) + (5074846020060849/100000000000000 : ℝ)*(sp5) + (1268713694862957/25000000000000 : ℝ)*(sp6) + (1298675094442139/50000000000000 : ℝ)*(sp7) + (1298683689782323/50000000000000 : ℝ)*(f.failure) + (634358095098941/12500000000000 : ℝ)*(f.sum) + (23580711241141/6947500000000000000000000000 : ℝ)*base65 + (3269818548657118189/277900000000000000000000000000000 : ℝ)*base68 + (233552688685718189/277900000000000000000000000000000 : ℝ)*base70 + (535133527005318189/277900000000000000000000000000000 : ℝ)*base72 + (46639981747249/6947500000000000000000000000 : ℝ)*base74 + (2351349159021481811/277900000000000000000000000000000 : ℝ)*base75 + (309229149175481811/277900000000000000000000000000000 : ℝ)*base77 + (944529081269518189/277900000000000000000000000000000 : ℝ)*base80 + (1348296531479/6947500000000000000000000000 : ℝ)*base82 + (168101/156250000000000000000 : ℝ)*base90 + (168101/156250000000000000000 : ℝ)*base92 + (168101/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29607/50000 : ℝ) ≤ (164562775435372971278525322167667/277900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15644883/100000000000000 : ℝ)*(upper0) + (20365671/25000000000000 : ℝ)*(lower1) + (2870627/2500000000000 : ℝ)*(lower3) + (12496241/25000000000000 : ℝ)*(upper4) + (50774947/100000000000000 : ℝ)*(upper5) + (3888046178515053/100000000000000 : ℝ)*(major0) + (3888046178515053/100000000000000 : ℝ)*(major1) + (3888046178515053/100000000000000 : ℝ)*(major2) + (319793086623063/6250000000000 : ℝ)*(sp0) + (5116469283652023/100000000000000 : ℝ)*(sp1) + (1279086416977193/25000000000000 : ℝ)*(sp2) + (329958015387743/12500000000000 : ℝ)*(sp3) + (44020463397/20000000000000 : ℝ)*(sp9) + (85929515059/25000000000000 : ℝ)*(sp10) + (329958015387743/12500000000000 : ℝ)*(f.failure) + (319793086623063/6250000000000 : ℝ)*(f.sum) + (6360099095179/13895000000000000000000000000 : ℝ)*base65 + (3735530436496404111/555800000000000000000000000000000 : ℝ)*base68 + (147596401202795889/555800000000000000000000000000000 : ℝ)*base69 + (2196548216580004111/555800000000000000000000000000000 : ℝ)*base72 + (213593851270207/6947500000000000000000000000 : ℝ)*base73 + (4961176972376995889/555800000000000000000000000000000 : ℝ)*base75 + (3557880913973204111/555800000000000000000000000000000 : ℝ)*base78 + (10163202612848404111/555800000000000000000000000000000 : ℝ)*base80 + (9932870478759/13895000000000000000000000000 : ℝ)*base81 + (141383/19531250000000000000 : ℝ)*base90 + (141383/19531250000000000000 : ℝ)*base92 + (141383/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39729/50000 : ℝ) ≤ (110410355492323124803423999189059/138950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14705063/10000000000000 : ℝ)*(upper0) + (27360587/50000000000000 : ℝ)*(lower3) + (445170223/100000000000000 : ℝ)*(upper4) + (2178160624282381/50000000000000 : ℝ)*(major0) + (2178160624282381/50000000000000 : ℝ)*(major1) + (2178160624282381/50000000000000 : ℝ)*(major2) + (55538476213/100000000000000 : ℝ)*(sp1) + (422020850647/100000000000000 : ℝ)*(sp2) + (92527338481/50000000000000 : ℝ)*(sp3) + (9051221677/100000000000000 : ℝ)*(sp4) + (1432140541836371/25000000000000 : ℝ)*(sp8) + (1432128920022737/25000000000000 : ℝ)*(sp9) + (5728149197716513/100000000000000 : ℝ)*(sp10) + (73934984819323/2500000000000 : ℝ)*(sp11) + (1478792223724941/50000000000000 : ℝ)*(f.failure) + (5728571218567161/100000000000000 : ℝ)*(f.sum) + (91034525639031/13895000000000000000000000000 : ℝ)*base65 + (3321648787438693647/277900000000000000000000000000000 : ℝ)*base68 + (652914339888193647/277900000000000000000000000000000 : ℝ)*base70 + (354990709198893647/277900000000000000000000000000000 : ℝ)*base72 + (118495590145477/6947500000000000000000000000 : ℝ)*base74 + (3713479639410693647/277900000000000000000000000000000 : ℝ)*base76 + (855501986950206353/277900000000000000000000000000000 : ℝ)*base77 + (5827992335452806353/277900000000000000000000000000000 : ℝ)*base79 + (28631513806401/13895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1271867/156250000000000000000 : ℝ)*base90 + (1271867/156250000000000000000 : ℝ)*base92 + (1271867/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8287/10000 : ℝ) ≤ (-115144385535093557332804141750239/138950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357389103/50000000000000 : ℝ)*(lower0) + (28409733/20000000000000 : ℝ)*(upper3) + (898078471/100000000000000 : ℝ)*(lower4) + (548831903124829/12500000000000 : ℝ)*(major0) + (548831903124829/12500000000000 : ℝ)*(major1) + (2195327612499317/50000000000000 : ℝ)*(major2) + (20687642093/100000000000000 : ℝ)*(sp0) + (334515745543/100000000000000 : ℝ)*(sp5) + (253971318317/20000000000000 : ℝ)*(sp6) + (395106652027/100000000000000 : ℝ)*(sp7) + (1457004465640711/25000000000000 : ℝ)*(sp12) + (2913852017229697/50000000000000 : ℝ)*(sp13) + (728346086701669/12500000000000 : ℝ)*(sp14) + (372562411471163/12500000000000 : ℝ)*(sp15) + (745223599605333/25000000000000 : ℝ)*(f.failure) + (5828038550204937/100000000000000 : ℝ)*(f.sum) + (22642486047791/13895000000000000000000000000 : ℝ)*base66 + (168219874720833623/69475000000000000000000000000000 : ℝ)*base68 + (2651660791318488921/277900000000000000000000000000000 : ℝ)*base69 + (1447771865887408623/69475000000000000000000000000000 : ℝ)*base72 + (224461732559111/3473750000000000000000000000 : ℝ)*base73 + (2872390487448088921/277900000000000000000000000000000 : ℝ)*base75 + (1405980180995573623/69475000000000000000000000000000 : ℝ)*base78 + (4020839231181176377/69475000000000000000000000000000 : ℝ)*base79 + (285352099453/434218750000000000000000000 : ℝ)*base81 + (885029/78125000000000000000 : ℝ)*base89 + (885029/78125000000000000000 : ℝ)*base91 + (677471/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1030_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4602913/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29607/50000 : ℝ) else (39729/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8287/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1030_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4111/1024 : ℝ) ≤ p) (hpb : p ≤ (8223/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4602913/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29607/50000 : ℝ) else (39729/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8287/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1030_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
