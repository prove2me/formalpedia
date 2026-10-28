-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:23.034871+00:00
-- url     : https://prove2.me/submissions/3313d876-2d37-46fc-8acb-e19a8547fe83

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
theorem support_rectangle_w1183_s6_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-429481313/2000000000 : ℝ)*x 0 + (5392564237/10000000000 : ℝ)*x 1 + (5266118689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429481313/2000000000 : ℝ)^1047 ≤ (13052520110923/100000000000000 : ℝ)^791 := by
    have hnat : (429481313 : ℕ)^1047*100000000000000^791 ≤ 13052520110923^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429481313 2000000000 13052520110923 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392564237/10000000000 : ℝ)^1047 ≤ (11039091112269/25000000000000 : ℝ)^791 := by
    have hnat : (5392564237 : ℕ)^1047*25000000000000^791 ≤ 11039091112269^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392564237 10000000000 11039091112269 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266118689/10000000000 : ℝ)^1047 ≤ (5348889427847/12500000000000 : ℝ)^791 := by
    have hnat : (5266118689 : ℕ)^1047*12500000000000^791 ≤ 5348889427847^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266118689 10000000000 5348889427847 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429481313/2000000000 : ℝ), (5392564237/10000000000 : ℝ), (5266118689/10000000000 : ℝ)] ![(13052520110923/100000000000000 : ℝ), (11039091112269/25000000000000 : ℝ), (5348889427847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429481313/2000000000 : ℝ)|^1047 ≤ (13052520110923/100000000000000 : ℝ)^791
        have hw : |(-429481313/2000000000 : ℝ)|=(429481313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392564237/10000000000 : ℝ)|^1047 ≤ (11039091112269/25000000000000 : ℝ)^791
        have hw : |(5392564237/10000000000 : ℝ)|=(5392564237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266118689/10000000000 : ℝ)|^1047 ≤ (5348889427847/12500000000000 : ℝ)^791
        have hw : |(5266118689/10000000000 : ℝ)|=(5266118689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668082913/1250000000 : ℝ)*x 0 + (-2211535729/10000000000 : ℝ)*x 1 + (2633059373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668082913/1250000000 : ℝ)^1047 ≤ (4363793915149/10000000000000 : ℝ)^791 := by
    have hnat : (668082913 : ℕ)^1047*10000000000000^791 ≤ 4363793915149^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668082913 1250000000 4363793915149 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211535729/10000000000 : ℝ)^1047 ≤ (13570944791811/100000000000000 : ℝ)^791 := by
    have hnat : (2211535729 : ℕ)^1047*100000000000000^791 ≤ 13570944791811^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211535729 10000000000 13570944791811 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633059373/5000000000 : ℝ)^1047 ≤ (42791116035843/100000000000000 : ℝ)^791 := by
    have hnat : (2633059373 : ℕ)^1047*100000000000000^791 ≤ 42791116035843^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633059373 5000000000 42791116035843 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668082913/1250000000 : ℝ), (-2211535729/10000000000 : ℝ), (2633059373/5000000000 : ℝ)] ![(4363793915149/10000000000000 : ℝ), (13570944791811/100000000000000 : ℝ), (42791116035843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668082913/1250000000 : ℝ)|^1047 ≤ (4363793915149/10000000000000 : ℝ)^791
        have hw : |(668082913/1250000000 : ℝ)|=(668082913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211535729/10000000000 : ℝ)|^1047 ≤ (13570944791811/100000000000000 : ℝ)^791
        have hw : |(-2211535729/10000000000 : ℝ)|=(2211535729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633059373/5000000000 : ℝ)|^1047 ≤ (42791116035843/100000000000000 : ℝ)^791
        have hw : |(2633059373/5000000000 : ℝ)|=(2633059373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (41755183/78125000 : ℝ)*x 0 + (5266118557/10000000000 : ℝ)*x 1 + (-2211535821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41755183/78125000 : ℝ)^1047 ≤ (43637940448357/100000000000000 : ℝ)^791 := by
    have hnat : (41755183 : ℕ)^1047*100000000000000^791 ≤ 43637940448357^791*78125000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41755183 78125000 43637940448357 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266118557/10000000000 : ℝ)^1047 ≤ (21395557001521/50000000000000 : ℝ)^791 := by
    have hnat : (5266118557 : ℕ)^1047*50000000000000^791 ≤ 21395557001521^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266118557 10000000000 21395557001521 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211535821/10000000000 : ℝ)^1047 ≤ (542837821563/4000000000000 : ℝ)^791 := by
    have hnat : (2211535821 : ℕ)^1047*4000000000000^791 ≤ 542837821563^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211535821 10000000000 542837821563 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41755183/78125000 : ℝ), (5266118557/10000000000 : ℝ), (-2211535821/10000000000 : ℝ)] ![(43637940448357/100000000000000 : ℝ), (21395557001521/50000000000000 : ℝ), (542837821563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41755183/78125000 : ℝ)|^1047 ≤ (43637940448357/100000000000000 : ℝ)^791
        have hw : |(41755183/78125000 : ℝ)|=(41755183/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266118557/10000000000 : ℝ)|^1047 ≤ (21395557001521/50000000000000 : ℝ)^791
        have hw : |(5266118557/10000000000 : ℝ)|=(5266118557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211535821/10000000000 : ℝ)|^1047 ≤ (542837821563/4000000000000 : ℝ)^791
        have hw : |(-2211535821/10000000000 : ℝ)|=(2211535821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4358915583/10000000000 : ℝ)*x 0 + (846788029/2000000000 : ℝ)*x 1 + (2243762729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358915583/10000000000 : ℝ)^1047 ≤ (1041157849667/3125000000000 : ℝ)^791 := by
    have hnat : (4358915583 : ℕ)^1047*3125000000000^791 ≤ 1041157849667^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358915583 10000000000 1041157849667 3125000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846788029/2000000000 : ℝ)^1047 ≤ (6411712057241/20000000000000 : ℝ)^791 := by
    have hnat : (846788029 : ℕ)^1047*20000000000000^791 ≤ 6411712057241^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846788029 2000000000 6411712057241 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243762729/5000000000 : ℝ)^1047 ≤ (8656097130229/25000000000000 : ℝ)^791 := by
    have hnat : (2243762729 : ℕ)^1047*25000000000000^791 ≤ 8656097130229^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243762729 5000000000 8656097130229 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358915583/10000000000 : ℝ), (846788029/2000000000 : ℝ), (2243762729/5000000000 : ℝ)] ![(1041157849667/3125000000000 : ℝ), (6411712057241/20000000000000 : ℝ), (8656097130229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358915583/10000000000 : ℝ)|^1047 ≤ (1041157849667/3125000000000 : ℝ)^791
        have hw : |(4358915583/10000000000 : ℝ)|=(4358915583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846788029/2000000000 : ℝ)|^1047 ≤ (6411712057241/20000000000000 : ℝ)^791
        have hw : |(846788029/2000000000 : ℝ)|=(846788029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243762729/5000000000 : ℝ)|^1047 ≤ (8656097130229/25000000000000 : ℝ)^791
        have hw : |(2243762729/5000000000 : ℝ)|=(2243762729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-536852873/2500000000 : ℝ)*x 0 + (526643809/1000000000 : ℝ)*x 1 + (168507613/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536852873/2500000000 : ℝ)^1047 ≤ (6526279875433/50000000000000 : ℝ)^791 := by
    have hnat : (536852873 : ℕ)^1047*50000000000000^791 ≤ 6526279875433^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536852873 2500000000 6526279875433 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526643809/1000000000 : ℝ)^1047 ≤ (2139727539709/5000000000000 : ℝ)^791 := by
    have hnat : (526643809 : ℕ)^1047*5000000000000^791 ≤ 2139727539709^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526643809 1000000000 2139727539709 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168507613/312500000 : ℝ)^1047 ≤ (22076444719909/50000000000000 : ℝ)^791 := by
    have hnat : (168507613 : ℕ)^1047*50000000000000^791 ≤ 22076444719909^791*312500000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168507613 312500000 22076444719909 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536852873/2500000000 : ℝ), (526643809/1000000000 : ℝ), (168507613/312500000 : ℝ)] ![(6526279875433/50000000000000 : ℝ), (2139727539709/5000000000000 : ℝ), (22076444719909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536852873/2500000000 : ℝ)|^1047 ≤ (6526279875433/50000000000000 : ℝ)^791
        have hw : |(-536852873/2500000000 : ℝ)|=(536852873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526643809/1000000000 : ℝ)|^1047 ≤ (2139727539709/5000000000000 : ℝ)^791
        have hw : |(526643809/1000000000 : ℝ)|=(526643809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168507613/312500000 : ℝ)|^1047 ≤ (22076444719909/50000000000000 : ℝ)^791
        have hw : |(168507613/312500000 : ℝ)|=(168507613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312532153/10000000000 : ℝ)*x 0 + (-130338171/625000000 : ℝ)*x 1 + (1348060909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312532153/10000000000 : ℝ)^1047 ≤ (169105581793/390625000000 : ℝ)^791 := by
    have hnat : (5312532153 : ℕ)^1047*390625000000^791 ≤ 169105581793^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312532153 10000000000 169105581793 390625000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130338171/625000000 : ℝ)^1047 ≤ (251121627661/2000000000000 : ℝ)^791 := by
    have hnat : (130338171 : ℕ)^1047*2000000000000^791 ≤ 251121627661^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130338171 625000000 251121627661 2000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348060909/2500000000 : ℝ)^1047 ≤ (44152889656583/100000000000000 : ℝ)^791 := by
    have hnat : (1348060909 : ℕ)^1047*100000000000000^791 ≤ 44152889656583^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348060909 2500000000 44152889656583 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312532153/10000000000 : ℝ), (-130338171/625000000 : ℝ), (1348060909/2500000000 : ℝ)] ![(169105581793/390625000000 : ℝ), (251121627661/2000000000000 : ℝ), (44152889656583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312532153/10000000000 : ℝ)|^1047 ≤ (169105581793/390625000000 : ℝ)^791
        have hw : |(5312532153/10000000000 : ℝ)|=(5312532153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130338171/625000000 : ℝ)|^1047 ≤ (251121627661/2000000000000 : ℝ)^791
        have hw : |(-130338171/625000000 : ℝ)|=(130338171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348060909/2500000000 : ℝ)|^1047 ≤ (44152889656583/100000000000000 : ℝ)^791
        have hw : |(1348060909/2500000000 : ℝ)|=(1348060909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656266087/5000000000 : ℝ)*x 0 + (2696121811/5000000000 : ℝ)*x 1 + (-2085410727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656266087/5000000000 : ℝ)^1047 ≤ (21645514582759/50000000000000 : ℝ)^791 := by
    have hnat : (2656266087 : ℕ)^1047*50000000000000^791 ≤ 21645514582759^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656266087 5000000000 21645514582759 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696121811/5000000000 : ℝ)^1047 ≤ (2759555594053/6250000000000 : ℝ)^791 := by
    have hnat : (2696121811 : ℕ)^1047*6250000000000^791 ≤ 2759555594053^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696121811 5000000000 2759555594053 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085410727/10000000000 : ℝ)^1047 ≤ (502243252453/4000000000000 : ℝ)^791 := by
    have hnat : (2085410727 : ℕ)^1047*4000000000000^791 ≤ 502243252453^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085410727 10000000000 502243252453 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656266087/5000000000 : ℝ), (2696121811/5000000000 : ℝ), (-2085410727/10000000000 : ℝ)] ![(21645514582759/50000000000000 : ℝ), (2759555594053/6250000000000 : ℝ), (502243252453/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656266087/5000000000 : ℝ)|^1047 ≤ (21645514582759/50000000000000 : ℝ)^791
        have hw : |(2656266087/5000000000 : ℝ)|=(2656266087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696121811/5000000000 : ℝ)|^1047 ≤ (2759555594053/6250000000000 : ℝ)^791
        have hw : |(2696121811/5000000000 : ℝ)|=(2696121811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085410727/10000000000 : ℝ)|^1047 ≤ (502243252453/4000000000000 : ℝ)^791
        have hw : |(-2085410727/10000000000 : ℝ)|=(2085410727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s6_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4358925081/10000000000 : ℝ)*x 0 + (4486884697/10000000000 : ℝ)*x 1 + (529322933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358925081/10000000000 : ℝ)^1047 ≤ (8329286820523/25000000000000 : ℝ)^791 := by
    have hnat : (4358925081 : ℕ)^1047*25000000000000^791 ≤ 8329286820523^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358925081 10000000000 8329286820523 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486884697/10000000000 : ℝ)^1047 ≤ (1384713787991/4000000000000 : ℝ)^791 := by
    have hnat : (4486884697 : ℕ)^1047*4000000000000^791 ≤ 1384713787991^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486884697 10000000000 1384713787991 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529322933/1250000000 : ℝ)^1047 ≤ (1282600320477/4000000000000 : ℝ)^791 := by
    have hnat : (529322933 : ℕ)^1047*4000000000000^791 ≤ 1282600320477^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529322933 1250000000 1282600320477 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358925081/10000000000 : ℝ), (4486884697/10000000000 : ℝ), (529322933/1250000000 : ℝ)] ![(8329286820523/25000000000000 : ℝ), (1384713787991/4000000000000 : ℝ), (1282600320477/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358925081/10000000000 : ℝ)|^1047 ≤ (8329286820523/25000000000000 : ℝ)^791
        have hw : |(4358925081/10000000000 : ℝ)|=(4358925081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486884697/10000000000 : ℝ)|^1047 ≤ (1384713787991/4000000000000 : ℝ)^791
        have hw : |(4486884697/10000000000 : ℝ)|=(4486884697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529322933/1250000000 : ℝ)|^1047 ≤ (1282600320477/4000000000000 : ℝ)^791
        have hw : |(529322933/1250000000 : ℝ)|=(529322933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5687/50000 : ℝ) ^ (8375/2048 : ℝ) ≤ (3445351912776927/25000000000000000000 : ℝ) := by
    have hpowers : (5687/50000 : ℝ)^8375 ≤ (3445351912776927/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5687 : ℕ)^8375*25000000000000000000^2048 ≤ 3445351912776927^2048*50000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5687 50000 3445351912776927 25000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5687/50000 : ℝ)) (X := (3445351912776927/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7053/50000 : ℝ) ^ (8375/2048 : ℝ) ≤ (16228566171179/48828125000000000 : ℝ) := by
    have hpowers : (7053/50000 : ℝ)^8375 ≤ (16228566171179/48828125000000000 : ℝ)^2048 := by
      have hnat : (7053 : ℕ)^8375*48828125000000000^2048 ≤ 16228566171179^2048*50000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7053 50000 16228566171179 48828125000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7053/50000 : ℝ)) (X := (16228566171179/48828125000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503445351912776927/12500000000000000000 : ℝ) ≤ (1000067394351793/1000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (12503445351912776927/12500000000000000000 : ℝ)^2048 ≤ (1000067394351793/1000000000000000 : ℝ)^8375 := by
      have hnat : (12503445351912776927 : ℕ)^2048*1000000000000000^8375 ≤ 1000067394351793^8375*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503445351912776927 12500000000000000000 1000067394351793 1000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000067394351793/1000000000000000 : ℝ)) (X := (12503445351912776927/12500000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000470175111696823/1000000000000000000 : ℝ) ≤ (125014369368083/125000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (1000470175111696823/1000000000000000000 : ℝ)^2048 ≤ (125014369368083/125000000000000 : ℝ)^8375 := by
      have hnat : (1000470175111696823 : ℕ)^2048*125000000000000^8375 ≤ 125014369368083^8375*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000470175111696823 1000000000000000000 125014369368083 125000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125014369368083/125000000000000 : ℝ)) (X := (1000470175111696823/1000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (24430291066171179/24414062500000000 : ℝ) ≤ (200032503107507/200000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (24430291066171179/24414062500000000 : ℝ)^2048 ≤ (200032503107507/200000000000000 : ℝ)^8375 := by
      have hnat : (24430291066171179 : ℕ)^2048*200000000000000^8375 ≤ 200032503107507^8375*24414062500000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24430291066171179 24414062500000000 200032503107507 200000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200032503107507/200000000000000 : ℝ)) (X := (24430291066171179/24414062500000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3445351912776927/25000000000000000000 : ℝ) ≤ ((341387776625308621/341500000000000000 : ℝ)+2*(47560592871/27320000000000 : ℝ)*(5687/50000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (341387776625308621/341500000000000000 : ℝ)+2*(47560592871/27320000000000 : ℝ)*(5687/50000 : ℝ)=(1000067394351793/1000000000000000 : ℝ) by norm_num, show 1+2*(3445351912776927/25000000000000000000 : ℝ)=(12503445351912776927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16228566171179/48828125000000000 : ℝ)+(3445351912776927/25000000000000000000 : ℝ) ≤ ((341387776625308621/341500000000000000 : ℝ)+(47560592871/27320000000000 : ℝ)*((7053/50000 : ℝ)+(5687/50000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (341387776625308621/341500000000000000 : ℝ)+(47560592871/27320000000000 : ℝ)*((7053/50000 : ℝ)+(5687/50000 : ℝ))=(125014369368083/125000000000000 : ℝ) by norm_num, show 1+(16228566171179/48828125000000000 : ℝ)+(3445351912776927/25000000000000000000 : ℝ)=(1000470175111696823/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16228566171179/48828125000000000 : ℝ) ≤ ((341387776625308621/341500000000000000 : ℝ)+2*(47560592871/27320000000000 : ℝ)*(7053/50000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (341387776625308621/341500000000000000 : ℝ)+2*(47560592871/27320000000000 : ℝ)*(7053/50000 : ℝ)=(200032503107507/200000000000000 : ℝ) by norm_num, show 1+2*(16228566171179/48828125000000000 : ℝ)=(24430291066171179/24414062500000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (341387776625308621/341500000000000000 : ℝ)*(X 1 0+X 2 0)+(47560592871/27320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (341387776625308621/341500000000000000 : ℝ)) (alpha := (47560592871/27320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (341387776625308621/341500000000000000 : ℝ)*(X 0 1+X 2 1)+(47560592871/27320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (341387776625308621/341500000000000000 : ℝ)) (alpha := (47560592871/27320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (341387776625308621/341500000000000000 : ℝ)*(X 0 2+X 1 2)+(47560592871/27320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (341387776625308621/341500000000000000 : ℝ)) (alpha := (47560592871/27320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429481313/2000000000 : ℝ)*X 0 0+(5392564237/10000000000 : ℝ)*X 0 1+(5266118689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668082913/1250000000 : ℝ)*X 1 0+(-2211535729/10000000000 : ℝ)*X 1 1+(2633059373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41755183/78125000 : ℝ)*X 2 0+(5266118557/10000000000 : ℝ)*X 2 1+(-2211535821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358915583/10000000000 : ℝ)*X 0 0+(846788029/2000000000 : ℝ)*X 0 1+(2243762729/5000000000 : ℝ)*X 0 2+(4358915583/10000000000 : ℝ)*X 1 0+(846788029/2000000000 : ℝ)*X 1 1+(2243762729/5000000000 : ℝ)*X 1 2+(4358915583/10000000000 : ℝ)*X 2 0+(846788029/2000000000 : ℝ)*X 2 1+(2243762729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536852873/2500000000 : ℝ)*X 0 0+(526643809/1000000000 : ℝ)*X 0 1+(168507613/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312532153/10000000000 : ℝ)*X 1 0+(-130338171/625000000 : ℝ)*X 1 1+(1348060909/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656266087/5000000000 : ℝ)*X 2 0+(2696121811/5000000000 : ℝ)*X 2 1+(-2085410727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358925081/10000000000 : ℝ)*X 0 0+(4486884697/10000000000 : ℝ)*X 0 1+(529322933/1250000000 : ℝ)*X 0 2+(4358925081/10000000000 : ℝ)*X 1 0+(4486884697/10000000000 : ℝ)*X 1 1+(529322933/1250000000 : ℝ)*X 1 2+(4358925081/10000000000 : ℝ)*X 2 0+(4486884697/10000000000 : ℝ)*X 2 1+(529322933/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119660812863426066420582561/17075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201792853/100000000000000 : ℝ)*(base19) + (13869273/1250000000000 : ℝ)*(base23) + (169359819/100000000000000 : ℝ)*(lower2) + (314226309/100000000000000 : ℝ)*(upper3) + (25151579/100000000000000 : ℝ)*(lower4) + (5926041462188651/100000000000000 : ℝ)*(major0) + (5926041462188651/100000000000000 : ℝ)*(major1) + (5926041462188651/100000000000000 : ℝ)*(major2) + (7908575799861529/100000000000000 : ℝ)*(sp0) + (3954299182774581/50000000000000 : ℝ)*(sp1) + (3954299228900087/50000000000000 : ℝ)*(sp2) + (492932521005949/12500000000000 : ℝ)*(sp3) + (4753496097/20000000000000 : ℝ)*(sp4) + (22955389221/100000000000000 : ℝ)*(sp7) + (1971741561718407/50000000000000 : ℝ)*(f.failure) + (3954299783671007/50000000000000 : ℝ)*(f.sum) + (7175505815691/1366000000000000000000000000 : ℝ)*base66 + (478958472151422771/34150000000000000000000000000000 : ℝ)*base67 + (451158868834272771/34150000000000000000000000000000 : ℝ)*base69 + (530651826253672771/34150000000000000000000000000000 : ℝ)*base71 + (2812387409093/1366000000000000000000000000 : ℝ)*base74 + (196128662818622771/34150000000000000000000000000000 : ℝ)*base75 + (68626759622472771/34150000000000000000000000000000 : ℝ)*base77 + (570274995187172771/34150000000000000000000000000000 : ℝ)*base79 + (445270050259/273200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10089613/1000000000000000000000 : ℝ)*base89 + (10089613/1000000000000000000000 : ℝ)*base91 + (10089613/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94183058186587488776496693/8537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1986713697/100000000000000 : ℝ)*(base19) + (54597723/2500000000000 : ℝ)*(base23) + (45110559/20000000000000 : ℝ)*(upper3) + (9027819/12500000000000 : ℝ)*(lower4) + (220199637/100000000000000 : ℝ)*(upper5) + (5956145371909339/100000000000000 : ℝ)*(major0) + (5956145371909339/100000000000000 : ℝ)*(major1) + (5956145371909339/100000000000000 : ℝ)*(major2) + (55958346101/100000000000000 : ℝ)*(sp1) + (12177940747/20000000000000 : ℝ)*(sp2) + (7948774611866413/100000000000000 : ℝ)*(sp4) + (1589743333361323/20000000000000 : ℝ)*(sp5) + (3974355769126879/50000000000000 : ℝ)*(sp6) + (396351576422923/10000000000000 : ℝ)*(sp7) + (396351576422923/10000000000000 : ℝ)*(f.failure) + (7948774611866413/100000000000000 : ℝ)*(f.sum) + (80379307817/54640000000000000000000000 : ℝ)*base65 + (398045459443474019/34150000000000000000000000000000 : ℝ)*base67 + (287906325764274019/34150000000000000000000000000000 : ℝ)*base69 + (91647460735124019/34150000000000000000000000000000 : ℝ)*base71 + (7766308554263/1366000000000000000000000000 : ℝ)*base73 + (1091643921300574019/34150000000000000000000000000000 : ℝ)*base75 + (18839015496825981/34150000000000000000000000000000 : ℝ)*base78 + (695359775004324019/34150000000000000000000000000000 : ℝ)*base79 + (2091119517823/273200000000000000000000000 : ℝ)*base81 + (2867143/200000000000000000000 : ℝ)*base90 + (2867143/200000000000000000000 : ℝ)*base92 + (2867143/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1183_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s7_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-53685723/250000000 : ℝ)*x 0 + (2696151423/5000000000 : ℝ)*x 1 + (5266365369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53685723/250000000 : ℝ)^1047 ≤ (13052699967241/100000000000000 : ℝ)^791 := by
    have hnat : (53685723 : ℕ)^1047*100000000000000^791 ≤ 13052699967241^791*250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53685723 250000000 13052699967241 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696151423/5000000000 : ℝ)^1047 ≤ (1103838284787/2500000000000 : ℝ)^791 := by
    have hnat : (2696151423 : ℕ)^1047*2500000000000^791 ≤ 1103838284787^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696151423 5000000000 1103838284787 2500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266365369/10000000000 : ℝ)^1047 ≤ (42793768625253/100000000000000 : ℝ)^791 := by
    have hnat : (5266365369 : ℕ)^1047*100000000000000^791 ≤ 42793768625253^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266365369 10000000000 42793768625253 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53685723/250000000 : ℝ), (2696151423/5000000000 : ℝ), (5266365369/10000000000 : ℝ)] ![(13052699967241/100000000000000 : ℝ), (1103838284787/2500000000000 : ℝ), (42793768625253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53685723/250000000 : ℝ)|^1047 ≤ (13052699967241/100000000000000 : ℝ)^791
        have hw : |(-53685723/250000000 : ℝ)|=(53685723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696151423/5000000000 : ℝ)|^1047 ≤ (1103838284787/2500000000000 : ℝ)^791
        have hw : |(2696151423/5000000000 : ℝ)|=(2696151423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266365369/10000000000 : ℝ)|^1047 ≤ (42793768625253/100000000000000 : ℝ)^791
        have hw : |(5266365369/10000000000 : ℝ)|=(5266365369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668074639/1250000000 : ℝ)*x 0 + (-141523/640000 : ℝ)*x 1 + (526636563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668074639/1250000000 : ℝ)^1047 ≤ (1745488952051/4000000000000 : ℝ)^791 := by
    have hnat : (668074639 : ℕ)^1047*4000000000000^791 ≤ 1745488952051^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668074639 1250000000 1745488952051 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141523/640000 : ℝ)^1047 ≤ (3392251187321/25000000000000 : ℝ)^791 := by
    have hnat : (141523 : ℕ)^1047*25000000000000^791 ≤ 3392251187321^791*640000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141523 640000 3392251187321 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526636563/1000000000 : ℝ)^1047 ≤ (21396885716249/50000000000000 : ℝ)^791 := by
    have hnat : (526636563 : ℕ)^1047*50000000000000^791 ≤ 21396885716249^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526636563 1000000000 21396885716249 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668074639/1250000000 : ℝ), (-141523/640000 : ℝ), (526636563/1000000000 : ℝ)] ![(1745488952051/4000000000000 : ℝ), (3392251187321/25000000000000 : ℝ), (21396885716249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668074639/1250000000 : ℝ)|^1047 ≤ (1745488952051/4000000000000 : ℝ)^791
        have hw : |(668074639/1250000000 : ℝ)|=(668074639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141523/640000 : ℝ)|^1047 ≤ (3392251187321/25000000000000 : ℝ)^791
        have hw : |(-141523/640000 : ℝ)|=(141523/640000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526636563/1000000000 : ℝ)|^1047 ≤ (21396885716249/50000000000000 : ℝ)^791
        have hw : |(526636563/1000000000 : ℝ)|=(526636563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (21378389/40000000 : ℝ)*x 0 + (2633182897/5000000000 : ℝ)*x 1 + (-1105648237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21378389/40000000 : ℝ)^1047 ≤ (8727445058533/20000000000000 : ℝ)^791 := by
    have hnat : (21378389 : ℕ)^1047*20000000000000^791 ≤ 8727445058533^791*40000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21378389 40000000 8727445058533 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633182897/5000000000 : ℝ)^1047 ≤ (42793773196437/100000000000000 : ℝ)^791 := by
    have hnat : (2633182897 : ℕ)^1047*100000000000000^791 ≤ 42793773196437^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633182897 5000000000 42793773196437 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105648237/5000000000 : ℝ)^1047 ≤ (13569001492301/100000000000000 : ℝ)^791 := by
    have hnat : (1105648237 : ℕ)^1047*100000000000000^791 ≤ 13569001492301^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105648237 5000000000 13569001492301 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21378389/40000000 : ℝ), (2633182897/5000000000 : ℝ), (-1105648237/5000000000 : ℝ)] ![(8727445058533/20000000000000 : ℝ), (42793773196437/100000000000000 : ℝ), (13569001492301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21378389/40000000 : ℝ)|^1047 ≤ (8727445058533/20000000000000 : ℝ)^791
        have hw : |(21378389/40000000 : ℝ)|=(21378389/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633182897/5000000000 : ℝ)|^1047 ≤ (42793773196437/100000000000000 : ℝ)^791
        have hw : |(2633182897/5000000000 : ℝ)|=(2633182897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105648237/5000000000 : ℝ)|^1047 ≤ (13569001492301/100000000000000 : ℝ)^791
        have hw : |(-1105648237/5000000000 : ℝ)|=(1105648237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (544866093/1250000000 : ℝ)*x 0 + (4234448131/10000000000 : ℝ)*x 1 + (8763699/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544866093/1250000000 : ℝ)^1047 ≤ (33317184341253/100000000000000 : ℝ)^791 := by
    have hnat : (544866093 : ℕ)^1047*100000000000000^791 ≤ 33317184341253^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544866093 1250000000 33317184341253 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234448131/10000000000 : ℝ)^1047 ≤ (32063651597759/100000000000000 : ℝ)^791 := by
    have hnat : (4234448131 : ℕ)^1047*100000000000000^791 ≤ 32063651597759^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234448131 10000000000 32063651597759 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8763699/19531250 : ℝ)^1047 ≤ (4327395506061/12500000000000 : ℝ)^791 := by
    have hnat : (8763699 : ℕ)^1047*12500000000000^791 ≤ 4327395506061^791*19531250^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8763699 19531250 4327395506061 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544866093/1250000000 : ℝ), (4234448131/10000000000 : ℝ), (8763699/19531250 : ℝ)] ![(33317184341253/100000000000000 : ℝ), (32063651597759/100000000000000 : ℝ), (4327395506061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544866093/1250000000 : ℝ)|^1047 ≤ (33317184341253/100000000000000 : ℝ)^791
        have hw : |(544866093/1250000000 : ℝ)|=(544866093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234448131/10000000000 : ℝ)|^1047 ≤ (32063651597759/100000000000000 : ℝ)^791
        have hw : |(4234448131/10000000000 : ℝ)|=(4234448131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8763699/19531250 : ℝ)|^1047 ≤ (4327395506061/12500000000000 : ℝ)^791
        have hw : |(8763699/19531250 : ℝ)|=(8763699/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-107371663/500000000 : ℝ)*x 0 + (5266682423/10000000000 : ℝ)*x 1 + (269599249/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107371663/500000000 : ℝ)^1047 ≤ (13052734884619/100000000000000 : ℝ)^791 := by
    have hnat : (107371663 : ℕ)^1047*100000000000000^791 ≤ 13052734884619^791*500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107371663 500000000 13052734884619 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266682423/10000000000 : ℝ)^1047 ≤ (5349647350569/12500000000000 : ℝ)^791 := by
    have hnat : (5266682423 : ℕ)^1047*12500000000000^791 ≤ 5349647350569^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266682423 10000000000 5349647350569 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269599249/500000000 : ℝ)^1047 ≤ (44150086295697/100000000000000 : ℝ)^791 := by
    have hnat : (269599249 : ℕ)^1047*100000000000000^791 ≤ 44150086295697^791*500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269599249 500000000 44150086295697 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107371663/500000000 : ℝ), (5266682423/10000000000 : ℝ), (269599249/500000000 : ℝ)] ![(13052734884619/100000000000000 : ℝ), (5349647350569/12500000000000 : ℝ), (44150086295697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107371663/500000000 : ℝ)|^1047 ≤ (13052734884619/100000000000000 : ℝ)^791
        have hw : |(-107371663/500000000 : ℝ)|=(107371663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266682423/10000000000 : ℝ)|^1047 ≤ (5349647350569/12500000000000 : ℝ)^791
        have hw : |(5266682423/10000000000 : ℝ)|=(5266682423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269599249/500000000 : ℝ)|^1047 ≤ (44150086295697/100000000000000 : ℝ)^791
        have hw : |(269599249/500000000 : ℝ)|=(269599249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328148869/2500000000 : ℝ)*x 0 + (-2085676789/10000000000 : ℝ)*x 1 + (269599249/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328148869/2500000000 : ℝ)^1047 ≤ (43291711951827/100000000000000 : ℝ)^791 := by
    have hnat : (1328148869 : ℕ)^1047*100000000000000^791 ≤ 43291711951827^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328148869 2500000000 43291711951827 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085676789/10000000000 : ℝ)^1047 ≤ (6279100872107/50000000000000 : ℝ)^791 := by
    have hnat : (2085676789 : ℕ)^1047*50000000000000^791 ≤ 6279100872107^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085676789 10000000000 6279100872107 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269599249/500000000 : ℝ)^1047 ≤ (44150086295697/100000000000000 : ℝ)^791 := by
    have hnat : (269599249 : ℕ)^1047*100000000000000^791 ≤ 44150086295697^791*500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269599249 500000000 44150086295697 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328148869/2500000000 : ℝ), (-2085676789/10000000000 : ℝ), (269599249/500000000 : ℝ)] ![(43291711951827/100000000000000 : ℝ), (6279100872107/50000000000000 : ℝ), (44150086295697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328148869/2500000000 : ℝ)|^1047 ≤ (43291711951827/100000000000000 : ℝ)^791
        have hw : |(1328148869/2500000000 : ℝ)|=(1328148869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085676789/10000000000 : ℝ)|^1047 ≤ (6279100872107/50000000000000 : ℝ)^791
        have hw : |(-2085676789/10000000000 : ℝ)|=(2085676789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269599249/500000000 : ℝ)|^1047 ≤ (44150086295697/100000000000000 : ℝ)^791
        have hw : |(269599249/500000000 : ℝ)|=(269599249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328148869/2500000000 : ℝ)*x 0 + (269599249/500000000 : ℝ)*x 1 + (-2085676789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328148869/2500000000 : ℝ)^1047 ≤ (43291711951827/100000000000000 : ℝ)^791 := by
    have hnat : (1328148869 : ℕ)^1047*100000000000000^791 ≤ 43291711951827^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328148869 2500000000 43291711951827 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269599249/500000000 : ℝ)^1047 ≤ (44150086295697/100000000000000 : ℝ)^791 := by
    have hnat : (269599249 : ℕ)^1047*100000000000000^791 ≤ 44150086295697^791*500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269599249 500000000 44150086295697 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085676789/10000000000 : ℝ)^1047 ≤ (6279100872107/50000000000000 : ℝ)^791 := by
    have hnat : (2085676789 : ℕ)^1047*50000000000000^791 ≤ 6279100872107^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085676789 10000000000 6279100872107 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328148869/2500000000 : ℝ), (269599249/500000000 : ℝ), (-2085676789/10000000000 : ℝ)] ![(43291711951827/100000000000000 : ℝ), (44150086295697/100000000000000 : ℝ), (6279100872107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328148869/2500000000 : ℝ)|^1047 ≤ (43291711951827/100000000000000 : ℝ)^791
        have hw : |(1328148869/2500000000 : ℝ)|=(1328148869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269599249/500000000 : ℝ)|^1047 ≤ (44150086295697/100000000000000 : ℝ)^791
        have hw : |(269599249/500000000 : ℝ)|=(269599249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085676789/10000000000 : ℝ)|^1047 ≤ (6279100872107/50000000000000 : ℝ)^791
        have hw : |(-2085676789/10000000000 : ℝ)|=(2085676789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s7_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (34871503/80000000 : ℝ)*x 0 + (4486378653/10000000000 : ℝ)*x 1 + (2117543071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34871503/80000000 : ℝ)^1047 ≤ (16658638360547/50000000000000 : ℝ)^791 := by
    have hnat : (34871503 : ℕ)^1047*50000000000000^791 ≤ 16658638360547^791*80000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34871503 80000000 16658638360547 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486378653/10000000000 : ℝ)^1047 ≤ (3461267690013/10000000000000 : ℝ)^791 := by
    have hnat : (4486378653 : ℕ)^1047*10000000000000^791 ≤ 3461267690013^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486378653 10000000000 3461267690013 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117543071/5000000000 : ℝ)^1047 ≤ (32070046370521/100000000000000 : ℝ)^791 := by
    have hnat : (2117543071 : ℕ)^1047*100000000000000^791 ≤ 32070046370521^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117543071 5000000000 32070046370521 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34871503/80000000 : ℝ), (4486378653/10000000000 : ℝ), (2117543071/5000000000 : ℝ)] ![(16658638360547/50000000000000 : ℝ), (3461267690013/10000000000000 : ℝ), (32070046370521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34871503/80000000 : ℝ)|^1047 ≤ (16658638360547/50000000000000 : ℝ)^791
        have hw : |(34871503/80000000 : ℝ)|=(34871503/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486378653/10000000000 : ℝ)|^1047 ≤ (3461267690013/10000000000000 : ℝ)^791
        have hw : |(4486378653/10000000000 : ℝ)|=(4486378653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117543071/5000000000 : ℝ)|^1047 ≤ (32070046370521/100000000000000 : ℝ)^791
        have hw : |(2117543071/5000000000 : ℝ)|=(2117543071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    (2281/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (8375/2048 : ℝ) ≤ (13910690762293989/100000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^8375 ≤ (13910690762293989/100000000000000000000 : ℝ)^2048 := by
      have hnat : (57 : ℕ)^8375*100000000000000000000^2048 ≤ 13910690762293989^2048*500^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 13910690762293989 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (13910690762293989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (32976721052786171/100000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^8375 ≤ (32976721052786171/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14079 : ℕ)^8375*100000000000000000000^2048 ≤ 32976721052786171^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 32976721052786171 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (32976721052786171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013910690762293989/50000000000000000000 : ℝ) ≤ (5000340132552207/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50013910690762293989/50000000000000000000 : ℝ)^2048 ≤ (5000340132552207/5000000000000000 : ℝ)^8375 := by
      have hnat : (50013910690762293989 : ℕ)^2048*5000000000000000^8375 ≤ 5000340132552207^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013910690762293989 50000000000000000000 5000340132552207 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340132552207/5000000000000000 : ℝ)) (X := (50013910690762293989/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (625293046323844251/625000000000000000 : ℝ) ≤ (625071648072499/625000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (625293046323844251/625000000000000000 : ℝ)^2048 ≤ (625071648072499/625000000000000 : ℝ)^8375 := by
      have hnat : (625293046323844251 : ℕ)^2048*625000000000000^8375 ≤ 625071648072499^8375*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625293046323844251 625000000000000000 625071648072499 625000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625071648072499/625000000000000 : ℝ)) (X := (625293046323844251/625000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032976721052786171/50000000000000000000 : ℝ) ≤ (5000806236607777/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50032976721052786171/50000000000000000000 : ℝ)^2048 ≤ (5000806236607777/5000000000000000 : ℝ)^8375 := by
      have hnat : (50032976721052786171 : ℕ)^2048*5000000000000000^8375 ≤ 5000806236607777^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032976721052786171 50000000000000000000 5000806236607777 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000806236607777/5000000000000000 : ℝ)) (X := (50032976721052786171/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13910690762293989/100000000000000000000 : ℝ) ≤ ((234922765418839729/235000000000000000 : ℝ)+2*(46610405557/26790000000000 : ℝ)*(57/500 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (234922765418839729/235000000000000000 : ℝ)+2*(46610405557/26790000000000 : ℝ)*(57/500 : ℝ)=(5000340132552207/5000000000000000 : ℝ) by norm_num, show 1+2*(13910690762293989/100000000000000000000 : ℝ)=(50013910690762293989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32976721052786171/100000000000000000000 : ℝ)+(13910690762293989/100000000000000000000 : ℝ) ≤ ((234922765418839729/235000000000000000 : ℝ)+(46610405557/26790000000000 : ℝ)*((14079/100000 : ℝ)+(57/500 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (234922765418839729/235000000000000000 : ℝ)+(46610405557/26790000000000 : ℝ)*((14079/100000 : ℝ)+(57/500 : ℝ))=(625071648072499/625000000000000 : ℝ) by norm_num, show 1+(32976721052786171/100000000000000000000 : ℝ)+(13910690762293989/100000000000000000000 : ℝ)=(625293046323844251/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32976721052786171/100000000000000000000 : ℝ) ≤ ((234922765418839729/235000000000000000 : ℝ)+2*(46610405557/26790000000000 : ℝ)*(14079/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (234922765418839729/235000000000000000 : ℝ)+2*(46610405557/26790000000000 : ℝ)*(14079/100000 : ℝ)=(5000806236607777/5000000000000000 : ℝ) by norm_num, show 1+2*(32976721052786171/100000000000000000000 : ℝ)=(50032976721052786171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (234922765418839729/235000000000000000 : ℝ)*(X 1 0+X 2 0)+(46610405557/26790000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (234922765418839729/235000000000000000 : ℝ)) (alpha := (46610405557/26790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (234922765418839729/235000000000000000 : ℝ)*(X 0 1+X 2 1)+(46610405557/26790000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (234922765418839729/235000000000000000 : ℝ)) (alpha := (46610405557/26790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (234922765418839729/235000000000000000 : ℝ)*(X 0 2+X 1 2)+(46610405557/26790000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (234922765418839729/235000000000000000 : ℝ)) (alpha := (46610405557/26790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53685723/250000000 : ℝ)*X 0 0+(2696151423/5000000000 : ℝ)*X 0 1+(5266365369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668074639/1250000000 : ℝ)*X 1 0+(-141523/640000 : ℝ)*X 1 1+(526636563/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21378389/40000000 : ℝ)*X 2 0+(2633182897/5000000000 : ℝ)*X 2 1+(-1105648237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544866093/1250000000 : ℝ)*X 0 0+(4234448131/10000000000 : ℝ)*X 0 1+(8763699/19531250 : ℝ)*X 0 2+(544866093/1250000000 : ℝ)*X 1 0+(4234448131/10000000000 : ℝ)*X 1 1+(8763699/19531250 : ℝ)*X 1 2+(544866093/1250000000 : ℝ)*X 2 0+(4234448131/10000000000 : ℝ)*X 2 1+(8763699/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107371663/500000000 : ℝ)*X 0 0+(5266682423/10000000000 : ℝ)*X 0 1+(269599249/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328148869/2500000000 : ℝ)*X 1 0+(-2085676789/10000000000 : ℝ)*X 1 1+(269599249/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328148869/2500000000 : ℝ)*X 2 0+(269599249/500000000 : ℝ)*X 2 1+(-2085676789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34871503/80000000 : ℝ)*X 0 0+(4486378653/10000000000 : ℝ)*X 0 1+(2117543071/5000000000 : ℝ)*X 0 2+(34871503/80000000 : ℝ)*X 1 0+(4486378653/10000000000 : ℝ)*X 1 1+(2117543071/5000000000 : ℝ)*X 1 2+(34871503/80000000 : ℝ)*X 2 0+(4486378653/10000000000 : ℝ)*X 2 1+(2117543071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1167790574619295054243/111625000000000000000000000 : ℝ) := by norm_num
    linear_combination (262453029/20000000000000 : ℝ)*(base19) + (16778403/1250000000000 : ℝ)*(base23) + (6491169/3125000000000 : ℝ)*(upper3) + (93541483/100000000000000 : ℝ)*(upper4) + (769452453/100000000000000 : ℝ)*(upper5) + (59499552021989/1000000000000 : ℝ)*(major0) + (59499552021989/1000000000000 : ℝ)*(major1) + (59499552021989/1000000000000 : ℝ)*(major2) + (39702320634601/500000000000 : ℝ)*(sp0) + (7940512226393291/100000000000000 : ℝ)*(sp1) + (1985128049096549/25000000000000 : ℝ)*(sp2) + (3959385379492909/100000000000000 : ℝ)*(sp3) + (12352934559/25000000000000 : ℝ)*(sp4) + (11137522127/100000000000000 : ℝ)*(sp7) + (989849129253759/25000000000000 : ℝ)*(f.failure) + (1985128384664609/25000000000000 : ℝ)*(f.sum) + (3044595594181/2679000000000000000000000000 : ℝ)*base65 + (16997131243854083/13395000000000000000000000000000 : ℝ)*base68 + (83843639966285917/13395000000000000000000000000000 : ℝ)*base69 + (184339912686020917/13395000000000000000000000000000 : ℝ)*base71 + (1222803904963/535800000000000000000000000 : ℝ)*base74 + (56465492287464083/13395000000000000000000000000000 : ℝ)*base76 + (81213087854139083/13395000000000000000000000000000 : ℝ)*base78 + (171402678492725917/13395000000000000000000000000000 : ℝ)*base79 + (5813133871481/1339500000000000000000000000 : ℝ)*base81 + (1964981/500000000000000000000 : ℝ)*base89 + (1964981/500000000000000000000 : ℝ)*base91 + (1964981/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4456631268158771909002551/734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274482347/25000000000000 : ℝ)*(base19) + (597481821/50000000000000 : ℝ)*(base23) + (15201169/12500000000000 : ℝ)*(upper3) + (44169069/100000000000000 : ℝ)*(lower4) + (123905073/100000000000000 : ℝ)*(upper5) + (93438343668179/1562500000000 : ℝ)*(major0) + (93438343668179/1562500000000 : ℝ)*(major1) + (93438343668179/1562500000000 : ℝ)*(major2) + (30593866213/100000000000000 : ℝ)*(sp1) + (6580052873/20000000000000 : ℝ)*(sp2) + (7980682034643181/100000000000000 : ℝ)*(sp4) + (7980650342847581/100000000000000 : ℝ)*(sp5) + (3990323969707587/50000000000000 : ℝ)*(sp6) + (1989712876298457/50000000000000 : ℝ)*(sp7) + (1989712876298457/50000000000000 : ℝ)*(f.failure) + (7980682034643181/100000000000000 : ℝ)*(f.sum) + (5040210779237/1339500000000000000000000000 : ℝ)*base65 + (412396232755728901/41859375000000000000000000000000 : ℝ)*base68 + (58352954675341013/20929687500000000000000000000000 : ℝ)*base70 + (34193867014393847/5232421875000000000000000000000 : ℝ)*base72 + (1663763444801/1339500000000000000000000000 : ℝ)*base73 + (118455943814272069/10464843750000000000000000000000 : ℝ)*base76 + (141753147631778513/20929687500000000000000000000000 : ℝ)*base78 + (313686916891872263/20929687500000000000000000000000 : ℝ)*base80 + (1566580437979/669750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7052563/1000000000000000000000 : ℝ)*base89 + (7052563/1000000000000000000000 : ℝ)*base91 + (7052563/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1183_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s8_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147435441/10000000000 : ℝ)*x 0 + (1078449631/2000000000 : ℝ)*x 1 + (5266415601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147435441/10000000000 : ℝ)^1047 ≤ (13052752431817/100000000000000 : ℝ)^791 := by
    have hnat : (2147435441 : ℕ)^1047*100000000000000^791 ≤ 13052752431817^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147435441 10000000000 13052752431817 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078449631/2000000000 : ℝ)^1047 ≤ (11038234658679/25000000000000 : ℝ)^791 := by
    have hnat : (1078449631 : ℕ)^1047*25000000000000^791 ≤ 11038234658679^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078449631 2000000000 11038234658679 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266415601/10000000000 : ℝ)^1047 ≤ (8558861781547/20000000000000 : ℝ)^791 := by
    have hnat : (5266415601 : ℕ)^1047*20000000000000^791 ≤ 8558861781547^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266415601 10000000000 8558861781547 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147435441/10000000000 : ℝ), (1078449631/2000000000 : ℝ), (5266415601/10000000000 : ℝ)] ![(13052752431817/100000000000000 : ℝ), (11038234658679/25000000000000 : ℝ), (8558861781547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147435441/10000000000 : ℝ)|^1047 ≤ (13052752431817/100000000000000 : ℝ)^791
        have hw : |(-2147435441/10000000000 : ℝ)|=(2147435441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078449631/2000000000 : ℝ)|^1047 ≤ (11038234658679/25000000000000 : ℝ)^791
        have hw : |(1078449631/2000000000 : ℝ)|=(1078449631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266415601/10000000000 : ℝ)|^1047 ≤ (8558861781547/20000000000000 : ℝ)^791
        have hw : |(5266415601/10000000000 : ℝ)|=(5266415601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534458321/1000000000 : ℝ)*x 0 + (-2211249327/10000000000 : ℝ)*x 1 + (329150969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534458321/1000000000 : ℝ)^1047 ≤ (21818536779969/50000000000000 : ℝ)^791 := by
    have hnat : (534458321 : ℕ)^1047*50000000000000^791 ≤ 21818536779969^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534458321 1000000000 21818536779969 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211249327/10000000000 : ℝ)^1047 ≤ (339215463963/2500000000000 : ℝ)^791 := by
    have hnat : (2211249327 : ℕ)^1047*2500000000000^791 ≤ 339215463963^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211249327 10000000000 339215463963 2500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329150969/625000000 : ℝ)^1047 ≤ (42794307864427/100000000000000 : ℝ)^791 := by
    have hnat : (329150969 : ℕ)^1047*100000000000000^791 ≤ 42794307864427^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329150969 625000000 42794307864427 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534458321/1000000000 : ℝ), (-2211249327/10000000000 : ℝ), (329150969/625000000 : ℝ)] ![(21818536779969/50000000000000 : ℝ), (339215463963/2500000000000 : ℝ), (42794307864427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534458321/1000000000 : ℝ)|^1047 ≤ (21818536779969/50000000000000 : ℝ)^791
        have hw : |(534458321/1000000000 : ℝ)|=(534458321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211249327/10000000000 : ℝ)|^1047 ≤ (339215463963/2500000000000 : ℝ)^791
        have hw : |(-2211249327/10000000000 : ℝ)|=(2211249327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329150969/625000000 : ℝ)|^1047 ≤ (42794307864427/100000000000000 : ℝ)^791
        have hw : |(329150969/625000000 : ℝ)|=(329150969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344583173/10000000000 : ℝ)*x 0 + (1316603891/2500000000 : ℝ)*x 1 + (-2211249297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344583173/10000000000 : ℝ)^1047 ≤ (5454634145009/12500000000000 : ℝ)^791 := by
    have hnat : (5344583173 : ℕ)^1047*12500000000000^791 ≤ 5454634145009^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344583173 10000000000 5454634145009 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316603891/2500000000 : ℝ)^1047 ≤ (10698577127443/25000000000000 : ℝ)^791 := by
    have hnat : (1316603891 : ℕ)^1047*25000000000000^791 ≤ 10698577127443^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316603891 2500000000 10698577127443 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211249297/10000000000 : ℝ)^1047 ≤ (13568618314857/100000000000000 : ℝ)^791 := by
    have hnat : (2211249297 : ℕ)^1047*100000000000000^791 ≤ 13568618314857^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211249297 10000000000 13568618314857 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344583173/10000000000 : ℝ), (1316603891/2500000000 : ℝ), (-2211249297/10000000000 : ℝ)] ![(5454634145009/12500000000000 : ℝ), (10698577127443/25000000000000 : ℝ), (13568618314857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344583173/10000000000 : ℝ)|^1047 ≤ (5454634145009/12500000000000 : ℝ)^791
        have hw : |(5344583173/10000000000 : ℝ)|=(5344583173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316603891/2500000000 : ℝ)|^1047 ≤ (10698577127443/25000000000000 : ℝ)^791
        have hw : |(1316603891/2500000000 : ℝ)|=(1316603891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211249297/10000000000 : ℝ)|^1047 ≤ (13568618314857/100000000000000 : ℝ)^791
        have hw : |(-2211249297/10000000000 : ℝ)|=(2211249297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4358930919/10000000000 : ℝ)*x 0 + (1058638267/2500000000 : ℝ)*x 1 + (560863593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358930919/10000000000 : ℝ)^1047 ≤ (33317206346083/100000000000000 : ℝ)^791 := by
    have hnat : (4358930919 : ℕ)^1047*100000000000000^791 ≤ 33317206346083^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358930919 10000000000 33317206346083 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058638267/2500000000 : ℝ)^1047 ≤ (6412940671599/20000000000000 : ℝ)^791 := by
    have hnat : (1058638267 : ℕ)^1047*20000000000000^791 ≤ 6412940671599^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058638267 2500000000 6412940671599 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560863593/1250000000 : ℝ)^1047 ≤ (8654522569039/25000000000000 : ℝ)^791 := by
    have hnat : (560863593 : ℕ)^1047*25000000000000^791 ≤ 8654522569039^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560863593 1250000000 8654522569039 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358930919/10000000000 : ℝ), (1058638267/2500000000 : ℝ), (560863593/1250000000 : ℝ)] ![(33317206346083/100000000000000 : ℝ), (6412940671599/20000000000000 : ℝ), (8654522569039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358930919/10000000000 : ℝ)|^1047 ≤ (33317206346083/100000000000000 : ℝ)^791
        have hw : |(4358930919/10000000000 : ℝ)|=(4358930919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058638267/2500000000 : ℝ)|^1047 ≤ (6412940671599/20000000000000 : ℝ)^791
        have hw : |(1058638267/2500000000 : ℝ)|=(1058638267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560863593/1250000000 : ℝ)|^1047 ≤ (8654522569039/25000000000000 : ℝ)^791
        have hw : |(560863593/1250000000 : ℝ)|=(560863593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147440233/10000000000 : ℝ)*x 0 + (5266731971/10000000000 : ℝ)*x 1 + (5391930631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147440233/10000000000 : ℝ)^1047 ≤ (13052790985791/100000000000000 : ℝ)^791 := by
    have hnat : (2147440233 : ℕ)^1047*100000000000000^791 ≤ 13052790985791^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147440233 10000000000 13052790985791 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266731971/10000000000 : ℝ)^1047 ≤ (42797711740479/100000000000000 : ℝ)^791 := by
    have hnat : (5266731971 : ℕ)^1047*100000000000000^791 ≤ 42797711740479^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266731971 10000000000 42797711740479 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391930631/10000000000 : ℝ)^1047 ≤ (2207474862843/5000000000000 : ℝ)^791 := by
    have hnat : (5391930631 : ℕ)^1047*5000000000000^791 ≤ 2207474862843^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391930631 10000000000 2207474862843 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147440233/10000000000 : ℝ), (5266731971/10000000000 : ℝ), (5391930631/10000000000 : ℝ)] ![(13052790985791/100000000000000 : ℝ), (42797711740479/100000000000000 : ℝ), (2207474862843/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147440233/10000000000 : ℝ)|^1047 ≤ (13052790985791/100000000000000 : ℝ)^791
        have hw : |(-2147440233/10000000000 : ℝ)|=(2147440233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266731971/10000000000 : ℝ)|^1047 ≤ (42797711740479/100000000000000 : ℝ)^791
        have hw : |(5266731971/10000000000 : ℝ)|=(5266731971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391930631/10000000000 : ℝ)|^1047 ≤ (2207474862843/5000000000000 : ℝ)^791
        have hw : |(5391930631/10000000000 : ℝ)|=(5391930631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312607653/10000000000 : ℝ)*x 0 + (-260716777/1250000000 : ℝ)*x 1 + (673991329/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312607653/10000000000 : ℝ)^1047 ≤ (8658368659071/20000000000000 : ℝ)^791 := by
    have hnat : (5312607653 : ℕ)^1047*20000000000000^791 ≤ 8658368659071^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312607653 10000000000 8658368659071 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260716777/1250000000 : ℝ)^1047 ≤ (6279329715677/50000000000000 : ℝ)^791 := by
    have hnat : (260716777 : ℕ)^1047*50000000000000^791 ≤ 6279329715677^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260716777 1250000000 6279329715677 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673991329/1250000000 : ℝ)^1047 ≤ (22074748633849/50000000000000 : ℝ)^791 := by
    have hnat : (673991329 : ℕ)^1047*50000000000000^791 ≤ 22074748633849^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673991329 1250000000 22074748633849 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312607653/10000000000 : ℝ), (-260716777/1250000000 : ℝ), (673991329/1250000000 : ℝ)] ![(8658368659071/20000000000000 : ℝ), (6279329715677/50000000000000 : ℝ), (22074748633849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312607653/10000000000 : ℝ)|^1047 ≤ (8658368659071/20000000000000 : ℝ)^791
        have hw : |(5312607653/10000000000 : ℝ)|=(5312607653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260716777/1250000000 : ℝ)|^1047 ≤ (6279329715677/50000000000000 : ℝ)^791
        have hw : |(-260716777/1250000000 : ℝ)|=(260716777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673991329/1250000000 : ℝ)|^1047 ≤ (22074748633849/50000000000000 : ℝ)^791
        have hw : |(673991329/1250000000 : ℝ)|=(673991329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328151913/2500000000 : ℝ)*x 0 + (5391930633/10000000000 : ℝ)*x 1 + (-260716777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328151913/2500000000 : ℝ)^1047 ≤ (43291843284569/100000000000000 : ℝ)^791 := by
    have hnat : (1328151913 : ℕ)^1047*100000000000000^791 ≤ 43291843284569^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328151913 2500000000 43291843284569 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391930633/10000000000 : ℝ)^1047 ≤ (5518687159817/12500000000000 : ℝ)^791 := by
    have hnat : (5391930633 : ℕ)^1047*12500000000000^791 ≤ 5518687159817^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391930633 10000000000 5518687159817 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260716777/1250000000 : ℝ)^1047 ≤ (6279329715677/50000000000000 : ℝ)^791 := by
    have hnat : (260716777 : ℕ)^1047*50000000000000^791 ≤ 6279329715677^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260716777 1250000000 6279329715677 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328151913/2500000000 : ℝ), (5391930633/10000000000 : ℝ), (-260716777/1250000000 : ℝ)] ![(43291843284569/100000000000000 : ℝ), (5518687159817/12500000000000 : ℝ), (6279329715677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328151913/2500000000 : ℝ)|^1047 ≤ (43291843284569/100000000000000 : ℝ)^791
        have hw : |(1328151913/2500000000 : ℝ)|=(1328151913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391930633/10000000000 : ℝ)|^1047 ≤ (5518687159817/12500000000000 : ℝ)^791
        have hw : |(5391930633/10000000000 : ℝ)|=(5391930633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260716777/1250000000 : ℝ)|^1047 ≤ (6279329715677/50000000000000 : ℝ)^791
        have hw : |(-260716777/1250000000 : ℝ)|=(260716777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s8_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (871788103/2000000000 : ℝ)*x 0 + (2243137061/5000000000 : ℝ)*x 1 + (529398747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871788103/2000000000 : ℝ)^1047 ≤ (33317303430423/100000000000000 : ℝ)^791 := by
    have hnat : (871788103 : ℕ)^1047*100000000000000^791 ≤ 33317303430423^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871788103 2000000000 33317303430423 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243137061/5000000000 : ℝ)^1047 ≤ (34611609436889/100000000000000 : ℝ)^791 := by
    have hnat : (2243137061 : ℕ)^1047*100000000000000^791 ≤ 34611609436889^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243137061 5000000000 34611609436889 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529398747/1250000000 : ℝ)^1047 ≤ (6414217425267/20000000000000 : ℝ)^791 := by
    have hnat : (529398747 : ℕ)^1047*20000000000000^791 ≤ 6414217425267^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529398747 1250000000 6414217425267 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871788103/2000000000 : ℝ), (2243137061/5000000000 : ℝ), (529398747/1250000000 : ℝ)] ![(33317303430423/100000000000000 : ℝ), (34611609436889/100000000000000 : ℝ), (6414217425267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871788103/2000000000 : ℝ)|^1047 ≤ (33317303430423/100000000000000 : ℝ)^791
        have hw : |(871788103/2000000000 : ℝ)|=(871788103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243137061/5000000000 : ℝ)|^1047 ≤ (34611609436889/100000000000000 : ℝ)^791
        have hw : |(2243137061/5000000000 : ℝ)|=(2243137061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529398747/1250000000 : ℝ)|^1047 ≤ (6414217425267/20000000000000 : ℝ)^791
        have hw : |(529398747/1250000000 : ℝ)|=(529398747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5703/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2281/20000 : ℝ) ^ (8375/2048 : ℝ) ≤ (13935657565216381/100000000000000000000 : ℝ) := by
    have hpowers : (2281/20000 : ℝ)^8375 ≤ (13935657565216381/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2281 : ℕ)^8375*100000000000000000000^2048 ≤ 13935657565216381^2048*20000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2281 20000 13935657565216381 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2281/20000 : ℝ)) (X := (13935657565216381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (32919288797011127/100000000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^8375 ≤ (32919288797011127/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14073 : ℕ)^8375*100000000000000000000^2048 ≤ 32919288797011127^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 32919288797011127 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (32919288797011127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013935657565216381/50000000000000000000 : ℝ) ≤ (2000136297182117/2000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50013935657565216381/50000000000000000000 : ℝ)^2048 ≤ (2000136297182117/2000000000000000 : ℝ)^8375 := by
      have hnat : (50013935657565216381 : ℕ)^2048*2000000000000000^8375 ≤ 2000136297182117^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013935657565216381 50000000000000000000 2000136297182117 2000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136297182117/2000000000000000 : ℝ)) (X := (50013935657565216381/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011713736590556877/25000000000000000000 : ℝ) ≤ (5000572787769761/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (25011713736590556877/25000000000000000000 : ℝ)^2048 ≤ (5000572787769761/5000000000000000 : ℝ)^8375 := by
      have hnat : (25011713736590556877 : ℕ)^2048*5000000000000000^8375 ≤ 5000572787769761^8375*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011713736590556877 25000000000000000000 5000572787769761 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000572787769761/5000000000000000 : ℝ)) (X := (25011713736590556877/25000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032919288797011127/50000000000000000000 : ℝ) ≤ (10001609665168459/10000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50032919288797011127/50000000000000000000 : ℝ)^2048 ≤ (10001609665168459/10000000000000000 : ℝ)^8375 := by
      have hnat : (50032919288797011127 : ℕ)^2048*10000000000000000^8375 ≤ 10001609665168459^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032919288797011127 50000000000000000000 10001609665168459 10000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001609665168459/10000000000000000 : ℝ)) (X := (50032919288797011127/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13935657565216381/100000000000000000000 : ℝ) ≤ ((91969766620597889/92000000000000000 : ℝ)+2*(16003090653/9200000000000 : ℝ)*(2281/20000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (91969766620597889/92000000000000000 : ℝ)+2*(16003090653/9200000000000 : ℝ)*(2281/20000 : ℝ)=(2000136297182117/2000000000000000 : ℝ) by norm_num, show 1+2*(13935657565216381/100000000000000000000 : ℝ)=(50013935657565216381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32919288797011127/100000000000000000000 : ℝ)+(13935657565216381/100000000000000000000 : ℝ) ≤ ((91969766620597889/92000000000000000 : ℝ)+(16003090653/9200000000000 : ℝ)*((14073/100000 : ℝ)+(2281/20000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (91969766620597889/92000000000000000 : ℝ)+(16003090653/9200000000000 : ℝ)*((14073/100000 : ℝ)+(2281/20000 : ℝ))=(5000572787769761/5000000000000000 : ℝ) by norm_num, show 1+(32919288797011127/100000000000000000000 : ℝ)+(13935657565216381/100000000000000000000 : ℝ)=(25011713736590556877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32919288797011127/100000000000000000000 : ℝ) ≤ ((91969766620597889/92000000000000000 : ℝ)+2*(16003090653/9200000000000 : ℝ)*(14073/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (91969766620597889/92000000000000000 : ℝ)+2*(16003090653/9200000000000 : ℝ)*(14073/100000 : ℝ)=(10001609665168459/10000000000000000 : ℝ) by norm_num, show 1+2*(32919288797011127/100000000000000000000 : ℝ)=(50032919288797011127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (91969766620597889/92000000000000000 : ℝ)*(X 1 0+X 2 0)+(16003090653/9200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (91969766620597889/92000000000000000 : ℝ)) (alpha := (16003090653/9200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (91969766620597889/92000000000000000 : ℝ)*(X 0 1+X 2 1)+(16003090653/9200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (91969766620597889/92000000000000000 : ℝ)) (alpha := (16003090653/9200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (91969766620597889/92000000000000000 : ℝ)*(X 0 2+X 1 2)+(16003090653/9200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (91969766620597889/92000000000000000 : ℝ)) (alpha := (16003090653/9200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147435441/10000000000 : ℝ)*X 0 0+(1078449631/2000000000 : ℝ)*X 0 1+(5266415601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534458321/1000000000 : ℝ)*X 1 0+(-2211249327/10000000000 : ℝ)*X 1 1+(329150969/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344583173/10000000000 : ℝ)*X 2 0+(1316603891/2500000000 : ℝ)*X 2 1+(-2211249297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358930919/10000000000 : ℝ)*X 0 0+(1058638267/2500000000 : ℝ)*X 0 1+(560863593/1250000000 : ℝ)*X 0 2+(4358930919/10000000000 : ℝ)*X 1 0+(1058638267/2500000000 : ℝ)*X 1 1+(560863593/1250000000 : ℝ)*X 1 2+(4358930919/10000000000 : ℝ)*X 2 0+(1058638267/2500000000 : ℝ)*X 2 1+(560863593/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2147440233/10000000000 : ℝ)*X 0 0+(5266731971/10000000000 : ℝ)*X 0 1+(5391930631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312607653/10000000000 : ℝ)*X 1 0+(-260716777/1250000000 : ℝ)*X 1 1+(673991329/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328151913/2500000000 : ℝ)*X 2 0+(5391930633/10000000000 : ℝ)*X 2 1+(-260716777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871788103/2000000000 : ℝ)*X 0 0+(2243137061/5000000000 : ℝ)*X 0 1+(529398747/1250000000 : ℝ)*X 0 2+(871788103/2000000000 : ℝ)*X 1 0+(2243137061/5000000000 : ℝ)*X 1 1+(529398747/1250000000 : ℝ)*X 1 2+(871788103/2000000000 : ℝ)*X 2 0+(2243137061/5000000000 : ℝ)*X 2 1+(529398747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8976327233227165086761163/920000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242136479/12500000000000 : ℝ)*(base19) + (874113777/50000000000000 : ℝ)*(base23) + (71535567/100000000000000 : ℝ)*(lower2) + (112365439/50000000000000 : ℝ)*(upper3) + (164819589/100000000000000 : ℝ)*(upper5) + (1190988341105511/20000000000000 : ℝ)*(major0) + (1190988341105511/20000000000000 : ℝ)*(major1) + (1190988341105511/20000000000000 : ℝ)*(major2) + (7947119293446517/100000000000000 : ℝ)*(sp0) + (3973583182030697/50000000000000 : ℝ)*(sp1) + (7947166552925673/100000000000000 : ℝ)*(sp2) + (792537399891747/20000000000000 : ℝ)*(sp3) + (4900770671/10000000000000 : ℝ)*(sp4) + (2778521389/10000000000000 : ℝ)*(sp7) + (1981357392336313/50000000000000 : ℝ)*(f.failure) + (3973584150576613/50000000000000 : ℝ)*(f.sum) + (28381883013/92000000000000000000000000 : ℝ)*base66 + (8791093546496279/1840000000000000000000000000000 : ℝ)*base67 + (12592900881183721/1840000000000000000000000000000 : ℝ)*base70 + (1178791918496279/1840000000000000000000000000000 : ℝ)*base71 + (171019909741/92000000000000000000000000 : ℝ)*base74 + (33649414516656279/1840000000000000000000000000000 : ℝ)*base75 + (39400394549263721/1840000000000000000000000000000 : ℝ)*base78 + (1082003176816279/1840000000000000000000000000000 : ℝ)*base79 + (6180067103/3680000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (17794867/1000000000000000000000 : ℝ)*base89 + (17794867/1000000000000000000000 : ℝ)*base91 + (17794867/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17097537212959501388988003/2300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1376144539/100000000000000 : ℝ)*(base19) + (29653717/2000000000000 : ℝ)*(base23) + (481486141/100000000000000 : ℝ)*(lower1) + (153449537/100000000000000 : ℝ)*(upper3) + (24610441/50000000000000 : ℝ)*(lower4) + (9757189/6250000000000 : ℝ)*(upper5) + (2992493850875009/50000000000000 : ℝ)*(major0) + (2992493850875009/50000000000000 : ℝ)*(major1) + (2992493850875009/50000000000000 : ℝ)*(major2) + (319739337/12500000000000 : ℝ)*(sp2) + (7987266268770571/100000000000000 : ℝ)*(sp4) + (7987264892626033/100000000000000 : ℝ)*(sp5) + (3993631114085013/50000000000000 : ℝ)*(sp6) + (199135444346953/5000000000000 : ℝ)*(sp7) + (199135444346953/5000000000000 : ℝ)*(f.failure) + (7987266268770571/100000000000000 : ℝ)*(f.sum) + (259994366233/230000000000000000000000000 : ℝ)*base66 + (111832844203573999/4600000000000000000000000000000 : ℝ)*base68 + (5887447863573999/4600000000000000000000000000000 : ℝ)*base70 + (106369003631626001/4600000000000000000000000000000 : ℝ)*base71 + (156230346717/230000000000000000000000000 : ℝ)*base73 + (50383972383426001/4600000000000000000000000000000 : ℝ)*base75 + (13749962898973999/4600000000000000000000000000000 : ℝ)*base78 + (19699028184173999/4600000000000000000000000000000 : ℝ)*base80 + (551370182483/230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1494627/100000000000000000000 : ℝ)*base89 + (1494627/100000000000000000000 : ℝ)*base91 + (1494627/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1183_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1183_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1183_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1183_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1183_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
