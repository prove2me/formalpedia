-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:43:07.827783+00:00
-- url     : https://prove2.me/submissions/f0418a62-8239-4f12-9862-78092750ed97

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
theorem support_rectangle_w1036_s9_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109314959/5000000000 : ℝ)*x 0 + (2697426801/5000000000 : ℝ)*x 1 + (5263908531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109314959/5000000000 : ℝ)^8229 ≤ (3367890475023/25000000000000 : ℝ)^6181 := by
    have hnat : (1109314959 : ℕ)^8229*25000000000000^6181 ≤ 3367890475023^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109314959 5000000000 3367890475023 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697426801/5000000000 : ℝ)^8229 ≤ (21985905342303/50000000000000 : ℝ)^6181 := by
    have hnat : (2697426801 : ℕ)^8229*50000000000000^6181 ≤ 21985905342303^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697426801 5000000000 21985905342303 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263908531/10000000000 : ℝ)^8229 ≤ (21278313699111/50000000000000 : ℝ)^6181 := by
    have hnat : (5263908531 : ℕ)^8229*50000000000000^6181 ≤ 21278313699111^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263908531 10000000000 21278313699111 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109314959/5000000000 : ℝ), (2697426801/5000000000 : ℝ), (5263908531/10000000000 : ℝ)] ![(3367890475023/25000000000000 : ℝ), (21985905342303/50000000000000 : ℝ), (21278313699111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109314959/5000000000 : ℝ)|^8229 ≤ (3367890475023/25000000000000 : ℝ)^6181
        have hw : |(-1109314959/5000000000 : ℝ)|=(1109314959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697426801/5000000000 : ℝ)|^8229 ≤ (21985905342303/50000000000000 : ℝ)^6181
        have hw : |(2697426801/5000000000 : ℝ)|=(2697426801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263908531/10000000000 : ℝ)|^8229 ≤ (21278313699111/50000000000000 : ℝ)^6181
        have hw : |(5263908531/10000000000 : ℝ)|=(5263908531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345032733/10000000000 : ℝ)*x 0 + (-2285075763/10000000000 : ℝ)*x 1 + (1315977231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345032733/10000000000 : ℝ)^8229 ≤ (43432016779203/100000000000000 : ℝ)^6181 := by
    have hnat : (5345032733 : ℕ)^8229*100000000000000^6181 ≤ 43432016779203^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345032733 10000000000 43432016779203 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285075763/10000000000 : ℝ)^8229 ≤ (1401135157827/10000000000000 : ℝ)^6181 := by
    have hnat : (2285075763 : ℕ)^8229*10000000000000^6181 ≤ 1401135157827^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285075763 10000000000 1401135157827 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315977231/2500000000 : ℝ)^8229 ≤ (5319578953527/12500000000000 : ℝ)^6181 := by
    have hnat : (1315977231 : ℕ)^8229*12500000000000^6181 ≤ 5319578953527^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315977231 2500000000 5319578953527 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345032733/10000000000 : ℝ), (-2285075763/10000000000 : ℝ), (1315977231/2500000000 : ℝ)] ![(43432016779203/100000000000000 : ℝ), (1401135157827/10000000000000 : ℝ), (5319578953527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345032733/10000000000 : ℝ)|^8229 ≤ (43432016779203/100000000000000 : ℝ)^6181
        have hw : |(5345032733/10000000000 : ℝ)|=(5345032733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285075763/10000000000 : ℝ)|^8229 ≤ (1401135157827/10000000000000 : ℝ)^6181
        have hw : |(-2285075763/10000000000 : ℝ)|=(2285075763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315977231/2500000000 : ℝ)|^8229 ≤ (5319578953527/12500000000000 : ℝ)^6181
        have hw : |(1315977231/2500000000 : ℝ)|=(1315977231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672516859/5000000000 : ℝ)*x 0 + (1315977069/2500000000 : ℝ)*x 1 + (-142817207/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672516859/5000000000 : ℝ)^8229 ≤ (43432027434957/100000000000000 : ℝ)^6181 := by
    have hnat : (2672516859 : ℕ)^8229*100000000000000^6181 ≤ 43432027434957^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672516859 5000000000 43432027434957 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315977069/2500000000 : ℝ)^8229 ≤ (42556624653569/100000000000000 : ℝ)^6181 := by
    have hnat : (1315977069 : ℕ)^8229*100000000000000^6181 ≤ 42556624653569^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315977069 2500000000 42556624653569 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142817207/625000000 : ℝ)^8229 ≤ (2802269579321/20000000000000 : ℝ)^6181 := by
    have hnat : (142817207 : ℕ)^8229*20000000000000^6181 ≤ 2802269579321^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142817207 625000000 2802269579321 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672516859/5000000000 : ℝ), (1315977069/2500000000 : ℝ), (-142817207/625000000 : ℝ)] ![(43432027434957/100000000000000 : ℝ), (42556624653569/100000000000000 : ℝ), (2802269579321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672516859/5000000000 : ℝ)|^8229 ≤ (43432027434957/100000000000000 : ℝ)^6181
        have hw : |(2672516859/5000000000 : ℝ)|=(2672516859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315977069/2500000000 : ℝ)|^8229 ≤ (42556624653569/100000000000000 : ℝ)^6181
        have hw : |(1315977069/2500000000 : ℝ)|=(1315977069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142817207/625000000 : ℝ)|^8229 ≤ (2802269579321/20000000000000 : ℝ)^6181
        have hw : |(-142817207/625000000 : ℝ)|=(142817207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547478189/1250000000 : ℝ)*x 0 + (4254168381/10000000000 : ℝ)*x 1 + (2254636643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547478189/1250000000 : ℝ)^8229 ≤ (16658191095427/50000000000000 : ℝ)^6181 := by
    have hnat : (547478189 : ℕ)^8229*50000000000000^6181 ≤ 16658191095427^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547478189 1250000000 16658191095427 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254168381/10000000000 : ℝ)^8229 ≤ (32049915068659/100000000000000 : ℝ)^6181 := by
    have hnat : (4254168381 : ℕ)^8229*100000000000000^6181 ≤ 32049915068659^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254168381 10000000000 32049915068659 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254636643/5000000000 : ℝ)^8229 ≤ (6926740544907/20000000000000 : ℝ)^6181 := by
    have hnat : (2254636643 : ℕ)^8229*20000000000000^6181 ≤ 6926740544907^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254636643 5000000000 6926740544907 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547478189/1250000000 : ℝ), (4254168381/10000000000 : ℝ), (2254636643/5000000000 : ℝ)] ![(16658191095427/50000000000000 : ℝ), (32049915068659/100000000000000 : ℝ), (6926740544907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547478189/1250000000 : ℝ)|^8229 ≤ (16658191095427/50000000000000 : ℝ)^6181
        have hw : |(547478189/1250000000 : ℝ)|=(547478189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254168381/10000000000 : ℝ)|^8229 ≤ (32049915068659/100000000000000 : ℝ)^6181
        have hw : |(4254168381/10000000000 : ℝ)|=(4254168381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254636643/5000000000 : ℝ)|^8229 ≤ (6926740544907/20000000000000 : ℝ)^6181
        have hw : |(2254636643/5000000000 : ℝ)|=(2254636643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218635153/10000000000 : ℝ)*x 0 + (2632118093/5000000000 : ℝ)*x 1 + (2697262349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218635153/10000000000 : ℝ)^8229 ≤ (13471604219371/100000000000000 : ℝ)^6181 := by
    have hnat : (2218635153 : ℕ)^8229*100000000000000^6181 ≤ 13471604219371^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218635153 10000000000 13471604219371 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632118093/5000000000 : ℝ)^8229 ≤ (21280077048899/50000000000000 : ℝ)^6181 := by
    have hnat : (2632118093 : ℕ)^8229*50000000000000^6181 ≤ 21280077048899^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632118093 5000000000 21280077048899 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697262349/5000000000 : ℝ)^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181 := by
    have hnat : (2697262349 : ℕ)^8229*50000000000000^6181 ≤ 21984120837269^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697262349 5000000000 21984120837269 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218635153/10000000000 : ℝ), (2632118093/5000000000 : ℝ), (2697262349/5000000000 : ℝ)] ![(13471604219371/100000000000000 : ℝ), (21280077048899/50000000000000 : ℝ), (21984120837269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218635153/10000000000 : ℝ)|^8229 ≤ (13471604219371/100000000000000 : ℝ)^6181
        have hw : |(-2218635153/10000000000 : ℝ)|=(2218635153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632118093/5000000000 : ℝ)|^8229 ≤ (21280077048899/50000000000000 : ℝ)^6181
        have hw : |(2632118093/5000000000 : ℝ)|=(2632118093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697262349/5000000000 : ℝ)|^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181
        have hw : |(2697262349/5000000000 : ℝ)|=(2697262349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656065349/5000000000 : ℝ)*x 0 + (-2154459133/10000000000 : ℝ)*x 1 + (2697262349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656065349/5000000000 : ℝ)^8229 ≤ (43076445251153/100000000000000 : ℝ)^6181 := by
    have hnat : (2656065349 : ℕ)^8229*100000000000000^6181 ≤ 43076445251153^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656065349 5000000000 43076445251153 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154459133/10000000000 : ℝ)^8229 ≤ (3238828267477/25000000000000 : ℝ)^6181 := by
    have hnat : (2154459133 : ℕ)^8229*25000000000000^6181 ≤ 3238828267477^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154459133 10000000000 3238828267477 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697262349/5000000000 : ℝ)^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181 := by
    have hnat : (2697262349 : ℕ)^8229*50000000000000^6181 ≤ 21984120837269^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697262349 5000000000 21984120837269 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656065349/5000000000 : ℝ), (-2154459133/10000000000 : ℝ), (2697262349/5000000000 : ℝ)] ![(43076445251153/100000000000000 : ℝ), (3238828267477/25000000000000 : ℝ), (21984120837269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656065349/5000000000 : ℝ)|^8229 ≤ (43076445251153/100000000000000 : ℝ)^6181
        have hw : |(2656065349/5000000000 : ℝ)|=(2656065349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154459133/10000000000 : ℝ)|^8229 ≤ (3238828267477/25000000000000 : ℝ)^6181
        have hw : |(-2154459133/10000000000 : ℝ)|=(2154459133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697262349/5000000000 : ℝ)|^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181
        have hw : |(2697262349/5000000000 : ℝ)|=(2697262349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656065349/5000000000 : ℝ)*x 0 + (2697262349/5000000000 : ℝ)*x 1 + (-2154459133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656065349/5000000000 : ℝ)^8229 ≤ (43076445251153/100000000000000 : ℝ)^6181 := by
    have hnat : (2656065349 : ℕ)^8229*100000000000000^6181 ≤ 43076445251153^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656065349 5000000000 43076445251153 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697262349/5000000000 : ℝ)^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181 := by
    have hnat : (2697262349 : ℕ)^8229*50000000000000^6181 ≤ 21984120837269^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697262349 5000000000 21984120837269 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154459133/10000000000 : ℝ)^8229 ≤ (3238828267477/25000000000000 : ℝ)^6181 := by
    have hnat : (2154459133 : ℕ)^8229*25000000000000^6181 ≤ 3238828267477^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154459133 10000000000 3238828267477 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656065349/5000000000 : ℝ), (2697262349/5000000000 : ℝ), (-2154459133/10000000000 : ℝ)] ![(43076445251153/100000000000000 : ℝ), (21984120837269/50000000000000 : ℝ), (3238828267477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656065349/5000000000 : ℝ)|^8229 ≤ (43076445251153/100000000000000 : ℝ)^6181
        have hw : |(2656065349/5000000000 : ℝ)|=(2656065349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697262349/5000000000 : ℝ)|^8229 ≤ (21984120837269/50000000000000 : ℝ)^6181
        have hw : |(2697262349/5000000000 : ℝ)|=(2697262349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154459133/10000000000 : ℝ)|^8229 ≤ (3238828267477/25000000000000 : ℝ)^6181
        have hw : |(-2154459133/10000000000 : ℝ)|=(2154459133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s9_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136869863/312500000 : ℝ)*x 0 + (901727137/2000000000 : ℝ)*x 1 + (1063702043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136869863/312500000 : ℝ)^8229 ≤ (2082280282257/6250000000000 : ℝ)^6181 := by
    have hnat : (136869863 : ℕ)^8229*6250000000000^6181 ≤ 2082280282257^6181*312500000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136869863 312500000 2082280282257 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901727137/2000000000 : ℝ)^8229 ≤ (865679578657/2500000000000 : ℝ)^6181 := by
    have hnat : (901727137 : ℕ)^8229*2500000000000^6181 ≤ 865679578657^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901727137 2000000000 865679578657 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063702043/2500000000 : ℝ)^8229 ≤ (16028166163129/50000000000000 : ℝ)^6181 := by
    have hnat : (1063702043 : ℕ)^8229*50000000000000^6181 ≤ 16028166163129^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063702043 2500000000 16028166163129 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136869863/312500000 : ℝ), (901727137/2000000000 : ℝ), (1063702043/2500000000 : ℝ)] ![(2082280282257/6250000000000 : ℝ), (865679578657/2500000000000 : ℝ), (16028166163129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136869863/312500000 : ℝ)|^8229 ≤ (2082280282257/6250000000000 : ℝ)^6181
        have hw : |(136869863/312500000 : ℝ)|=(136869863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901727137/2000000000 : ℝ)|^8229 ≤ (865679578657/2500000000000 : ℝ)^6181
        have hw : |(901727137/2000000000 : ℝ)|=(901727137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063702043/2500000000 : ℝ)|^8229 ≤ (16028166163129/50000000000000 : ℝ)^6181
        have hw : |(1063702043/2500000000 : ℝ)|=(1063702043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1121/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13983/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (437/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (437/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11209/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (15190100396834669/100000000000000000000 : ℝ) := by
    have hpowers : (11209/100000 : ℝ)^2057 ≤ (15190100396834669/100000000000000000000 : ℝ)^512 := by
      have hnat : (11209 : ℕ)^2057*100000000000000000000^512 ≤ 15190100396834669^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11209 100000 15190100396834669 100000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11209/100000 : ℝ)) (X := (15190100396834669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (437/3125 : ℝ) ^ (2057/512 : ℝ) ≤ (9235224815623807/25000000000000000000 : ℝ) := by
    have hpowers : (437/3125 : ℝ)^2057 ≤ (9235224815623807/25000000000000000000 : ℝ)^512 := by
      have hnat : (437 : ℕ)^2057*25000000000000000000^512 ≤ 9235224815623807^512*3125^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        437 3125 9235224815623807 25000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (437/3125 : ℝ)) (X := (9235224815623807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015190100396834669/50000000000000000000 : ℝ) ≤ (10000756095695667/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50015190100396834669/50000000000000000000 : ℝ)^512 ≤ (10000756095695667/10000000000000000 : ℝ)^2057 := by
      have hnat : (50015190100396834669 : ℕ)^512*10000000000000000^2057 ≤ 10000756095695667^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015190100396834669 50000000000000000000 10000756095695667 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000756095695667/10000000000000000 : ℝ)) (X := (50015190100396834669/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052130999659329897/100000000000000000000 : ℝ) ≤ (10001297318810607/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (100052130999659329897/100000000000000000000 : ℝ)^512 ≤ (10001297318810607/10000000000000000 : ℝ)^2057 := by
      have hnat : (100052130999659329897 : ℕ)^512*10000000000000000^2057 ≤ 10001297318810607^2057*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052130999659329897 100000000000000000000 10001297318810607 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001297318810607/10000000000000000 : ℝ)) (X := (100052130999659329897/100000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509235224815623807/12500000000000000000 : ℝ) ≤ (10001838541925547/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (12509235224815623807/12500000000000000000 : ℝ)^512 ≤ (10001838541925547/10000000000000000 : ℝ)^2057 := by
      have hnat : (12509235224815623807 : ℕ)^512*10000000000000000^2057 ≤ 10001838541925547^2057*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509235224815623807 12500000000000000000 10001838541925547 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001838541925547/10000000000000000 : ℝ)) (X := (12509235224815623807/12500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15190100396834669/100000000000000000000 : ℝ) ≤ ((1849331001717650067/1850000000000000000 : ℝ)+2*(9020385249/4625000000000 : ℝ)*(11209/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1849331001717650067/1850000000000000000 : ℝ)+2*(9020385249/4625000000000 : ℝ)*(11209/100000 : ℝ)=(10000756095695667/10000000000000000 : ℝ) by norm_num, show 1+2*(15190100396834669/100000000000000000000 : ℝ)=(50015190100396834669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9235224815623807/25000000000000000000 : ℝ)+(15190100396834669/100000000000000000000 : ℝ) ≤ ((1849331001717650067/1850000000000000000 : ℝ)+(9020385249/4625000000000 : ℝ)*((437/3125 : ℝ)+(11209/100000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (1849331001717650067/1850000000000000000 : ℝ)+(9020385249/4625000000000 : ℝ)*((437/3125 : ℝ)+(11209/100000 : ℝ))=(10001297318810607/10000000000000000 : ℝ) by norm_num, show 1+(9235224815623807/25000000000000000000 : ℝ)+(15190100396834669/100000000000000000000 : ℝ)=(100052130999659329897/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9235224815623807/25000000000000000000 : ℝ) ≤ ((1849331001717650067/1850000000000000000 : ℝ)+2*(9020385249/4625000000000 : ℝ)*(437/3125 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1849331001717650067/1850000000000000000 : ℝ)+2*(9020385249/4625000000000 : ℝ)*(437/3125 : ℝ)=(10001838541925547/10000000000000000 : ℝ) by norm_num, show 1+2*(9235224815623807/25000000000000000000 : ℝ)=(12509235224815623807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1849331001717650067/1850000000000000000 : ℝ)*(X 1 0+X 2 0)+(9020385249/4625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (1849331001717650067/1850000000000000000 : ℝ)) (alpha := (9020385249/4625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1849331001717650067/1850000000000000000 : ℝ)*(X 0 1+X 2 1)+(9020385249/4625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (1849331001717650067/1850000000000000000 : ℝ)) (alpha := (9020385249/4625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1849331001717650067/1850000000000000000 : ℝ)*(X 0 2+X 1 2)+(9020385249/4625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (1849331001717650067/1850000000000000000 : ℝ)) (alpha := (9020385249/4625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1109314959/5000000000 : ℝ)*X 0 0+(2697426801/5000000000 : ℝ)*X 0 1+(5263908531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345032733/10000000000 : ℝ)*X 1 0+(-2285075763/10000000000 : ℝ)*X 1 1+(1315977231/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672516859/5000000000 : ℝ)*X 2 0+(1315977069/2500000000 : ℝ)*X 2 1+(-142817207/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547478189/1250000000 : ℝ)*X 0 0+(4254168381/10000000000 : ℝ)*X 0 1+(2254636643/5000000000 : ℝ)*X 0 2+(547478189/1250000000 : ℝ)*X 1 0+(4254168381/10000000000 : ℝ)*X 1 1+(2254636643/5000000000 : ℝ)*X 1 2+(547478189/1250000000 : ℝ)*X 2 0+(4254168381/10000000000 : ℝ)*X 2 1+(2254636643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2218635153/10000000000 : ℝ)*X 0 0+(2632118093/5000000000 : ℝ)*X 0 1+(2697262349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656065349/5000000000 : ℝ)*X 1 0+(-2154459133/10000000000 : ℝ)*X 1 1+(2697262349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656065349/5000000000 : ℝ)*X 2 0+(2697262349/5000000000 : ℝ)*X 2 1+(-2154459133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136869863/312500000 : ℝ)*X 0 0+(901727137/2000000000 : ℝ)*X 0 1+(1063702043/2500000000 : ℝ)*X 0 2+(136869863/312500000 : ℝ)*X 1 0+(901727137/2000000000 : ℝ)*X 1 1+(1063702043/2500000000 : ℝ)*X 1 2+(136869863/312500000 : ℝ)*X 2 0+(901727137/2000000000 : ℝ)*X 2 1+(1063702043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354501105562602803239119831/46250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (577136463/100000000000000 : ℝ)*(base23) + (289466101/100000000000000 : ℝ)*(lower2) + (107197659/100000000000000 : ℝ)*(upper3) + (195407199/100000000000000 : ℝ)*(upper4) + (9324361/10000000000000 : ℝ)*(upper5) + (5778379721806369/100000000000000 : ℝ)*(major0) + (5778379721806369/100000000000000 : ℝ)*(major1) + (5778379721806369/100000000000000 : ℝ)*(major2) + (954598593302161/12500000000000 : ℝ)*(sp0) + (3818401758539459/50000000000000 : ℝ)*(sp1) + (3818407720087687/50000000000000 : ℝ)*(sp2) + (244996448175287/6250000000000 : ℝ)*(sp3) + (27270894549/100000000000000 : ℝ)*(sp4) + (6250116459/50000000000000 : ℝ)*(sp5) + (244996448175287/6250000000000 : ℝ)*(f.failure) + (7636816017311837/100000000000000 : ℝ)*(f.sum) + (18729473259749/925000000000000000000000000 : ℝ)*base65 + (1408637388656276723/185000000000000000000000000000000 : ℝ)*base67 + (1471841730343723277/185000000000000000000000000000000 : ℝ)*base70 + (7209985100456276723/185000000000000000000000000000000 : ℝ)*base71 + (1039729114081/231250000000000000000000000 : ℝ)*base73 + (2107368464446276723/185000000000000000000000000000000 : ℝ)*base75 + (1891027738766276723/185000000000000000000000000000000 : ℝ)*base77 + (4388585247866276723/185000000000000000000000000000000 : ℝ)*base79 + (801457994081/231250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3617279/625000000000000000000 : ℝ)*base90 + (3617279/625000000000000000000 : ℝ)*base92 + (3617279/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8628571534463658951522423/4625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350443109/100000000000000 : ℝ)*(base19) + (190611309/50000000000000 : ℝ)*(base23) + (123887207/100000000000000 : ℝ)*(lower1) + (37508529/100000000000000 : ℝ)*(upper3) + (876477/6250000000000 : ℝ)*(lower4) + (9598303/25000000000000 : ℝ)*(upper5) + (580747112442177/10000000000000 : ℝ)*(major0) + (580747112442177/10000000000000 : ℝ)*(major1) + (580747112442177/10000000000000 : ℝ)*(major2) + (176794947/25000000000000 : ℝ)*(sp2) + (7675263960264223/100000000000000 : ℝ)*(sp4) + (3837631804910557/50000000000000 : ℝ)*(sp5) + (7675262871861817/100000000000000 : ℝ)*(sp6) + (984919556597843/25000000000000 : ℝ)*(sp7) + (984919556597843/25000000000000 : ℝ)*(f.failure) + (7675263960264223/100000000000000 : ℝ)*(f.sum) + (493854719521/185000000000000000000000000 : ℝ)*base66 + (89793419673875859/18500000000000000000000000000000 : ℝ)*base67 + (122655185383875859/18500000000000000000000000000000 : ℝ)*base69 + (1687602949707124141/18500000000000000000000000000000 : ℝ)*base72 + (163409260073/92500000000000000000000000 : ℝ)*base74 + (5242426697900875859/18500000000000000000000000000000 : ℝ)*base75 + (234919039449875859/18500000000000000000000000000000 : ℝ)*base77 + (258420766567875859/18500000000000000000000000000000 : ℝ)*base79 + (249173614811/185000000000000000000000000 : ℝ)*base82 + (4898069/2500000000000000000000 : ℝ)*base89 + (4898069/2500000000000000000000 : ℝ)*base91 + (4898069/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_box_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-522031633/2500000000 : ℝ)*x 0 + (5377767429/10000000000 : ℝ)*x 1 + (672220883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522031633/2500000000 : ℝ)^8229 ≤ (12427003299547/100000000000000 : ℝ)^6181 := by
    have hnat : (522031633 : ℕ)^8229*100000000000000^6181 ≤ 12427003299547^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522031633 2500000000 12427003299547 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377767429/10000000000 : ℝ)^8229 ≤ (43786500319861/100000000000000 : ℝ)^6181 := by
    have hnat : (5377767429 : ℕ)^8229*100000000000000^6181 ≤ 43786500319861^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377767429 10000000000 43786500319861 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672220883/1250000000 : ℝ)^8229 ≤ (21893248181643/50000000000000 : ℝ)^6181 := by
    have hnat : (672220883 : ℕ)^8229*50000000000000^6181 ≤ 21893248181643^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672220883 1250000000 21893248181643 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522031633/2500000000 : ℝ), (5377767429/10000000000 : ℝ), (672220883/1250000000 : ℝ)] ![(12427003299547/100000000000000 : ℝ), (43786500319861/100000000000000 : ℝ), (21893248181643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522031633/2500000000 : ℝ)|^8229 ≤ (12427003299547/100000000000000 : ℝ)^6181
        have hw : |(-522031633/2500000000 : ℝ)|=(522031633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377767429/10000000000 : ℝ)|^8229 ≤ (43786500319861/100000000000000 : ℝ)^6181
        have hw : |(5377767429/10000000000 : ℝ)|=(5377767429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672220883/1250000000 : ℝ)|^8229 ≤ (21893248181643/50000000000000 : ℝ)^6181
        have hw : |(672220883/1250000000 : ℝ)|=(672220883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294853321/10000000000 : ℝ)*x 0 + (-2200286449/10000000000 : ℝ)*x 1 + (336110467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294853321/10000000000 : ℝ)^8229 ≤ (10722505187351/25000000000000 : ℝ)^6181 := by
    have hnat : (5294853321 : ℕ)^8229*25000000000000^6181 ≤ 10722505187351^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294853321 10000000000 10722505187351 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200286449/10000000000 : ℝ)^8229 ≤ (266469569197/2000000000000 : ℝ)^6181 := by
    have hnat : (2200286449 : ℕ)^8229*2000000000000^6181 ≤ 266469569197^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200286449 10000000000 266469569197 2000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336110467/625000000 : ℝ)^8229 ≤ (21893250392989/50000000000000 : ℝ)^6181 := by
    have hnat : (336110467 : ℕ)^8229*50000000000000^6181 ≤ 21893250392989^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336110467 625000000 21893250392989 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294853321/10000000000 : ℝ), (-2200286449/10000000000 : ℝ), (336110467/625000000 : ℝ)] ![(10722505187351/25000000000000 : ℝ), (266469569197/2000000000000 : ℝ), (21893250392989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294853321/10000000000 : ℝ)|^8229 ≤ (10722505187351/25000000000000 : ℝ)^6181
        have hw : |(5294853321/10000000000 : ℝ)|=(5294853321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200286449/10000000000 : ℝ)|^8229 ≤ (266469569197/2000000000000 : ℝ)^6181
        have hw : |(-2200286449/10000000000 : ℝ)|=(2200286449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336110467/625000000 : ℝ)|^8229 ≤ (21893250392989/50000000000000 : ℝ)^6181
        have hw : |(336110467/625000000 : ℝ)|=(336110467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294853713/10000000000 : ℝ)*x 0 + (2688883501/5000000000 : ℝ)*x 1 + (-440057311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294853713/10000000000 : ℝ)^8229 ≤ (42890024976837/100000000000000 : ℝ)^6181 := by
    have hnat : (5294853713 : ℕ)^8229*100000000000000^6181 ≤ 42890024976837^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294853713 10000000000 42890024976837 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688883501/5000000000 : ℝ)^8229 ≤ (43786495691211/100000000000000 : ℝ)^6181 := by
    have hnat : (2688883501 : ℕ)^8229*100000000000000^6181 ≤ 43786495691211^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688883501 5000000000 43786495691211 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440057311/2000000000 : ℝ)^8229 ≤ (13323479314391/100000000000000 : ℝ)^6181 := by
    have hnat : (440057311 : ℕ)^8229*100000000000000^6181 ≤ 13323479314391^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440057311 2000000000 13323479314391 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294853713/10000000000 : ℝ), (2688883501/5000000000 : ℝ), (-440057311/2000000000 : ℝ)] ![(42890024976837/100000000000000 : ℝ), (43786495691211/100000000000000 : ℝ), (13323479314391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294853713/10000000000 : ℝ)|^8229 ≤ (42890024976837/100000000000000 : ℝ)^6181
        have hw : |(5294853713/10000000000 : ℝ)|=(5294853713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688883501/5000000000 : ℝ)|^8229 ≤ (43786495691211/100000000000000 : ℝ)^6181
        have hw : |(2688883501/5000000000 : ℝ)|=(2688883501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440057311/2000000000 : ℝ)|^8229 ≤ (13323479314391/100000000000000 : ℝ)^6181
        have hw : |(-440057311/2000000000 : ℝ)|=(440057311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4488558739/10000000000 : ℝ)*x 0 + (2163822063/5000000000 : ℝ)*x 1 + (4327643841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488558739/10000000000 : ℝ)^8229 ≤ (34422049375579/100000000000000 : ℝ)^6181 := by
    have hnat : (4488558739 : ℕ)^8229*100000000000000^6181 ≤ 34422049375579^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488558739 10000000000 34422049375579 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163822063/5000000000 : ℝ)^8229 ≤ (16394488371243/50000000000000 : ℝ)^6181 := by
    have hnat : (2163822063 : ℕ)^8229*50000000000000^6181 ≤ 16394488371243^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163822063 5000000000 16394488371243 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4327643841/10000000000 : ℝ)^8229 ≤ (16394486933837/50000000000000 : ℝ)^6181 := by
    have hnat : (4327643841 : ℕ)^8229*50000000000000^6181 ≤ 16394486933837^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327643841 10000000000 16394486933837 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488558739/10000000000 : ℝ), (2163822063/5000000000 : ℝ), (4327643841/10000000000 : ℝ)] ![(34422049375579/100000000000000 : ℝ), (16394488371243/50000000000000 : ℝ), (16394486933837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488558739/10000000000 : ℝ)|^8229 ≤ (34422049375579/100000000000000 : ℝ)^6181
        have hw : |(4488558739/10000000000 : ℝ)|=(4488558739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2163822063/5000000000 : ℝ)|^8229 ≤ (16394488371243/50000000000000 : ℝ)^6181
        have hw : |(2163822063/5000000000 : ℝ)|=(2163822063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4327643841/10000000000 : ℝ)|^8229 ≤ (16394486933837/50000000000000 : ℝ)^6181
        have hw : |(4327643841/10000000000 : ℝ)|=(4327643841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2350521861/10000000000 : ℝ)*x 0 + (1055926233/2000000000 : ℝ)*x 1 + (1055926093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2350521861/10000000000 : ℝ)^8229 ≤ (2909625830397/20000000000000 : ℝ)^6181 := by
    have hnat : (2350521861 : ℕ)^8229*20000000000000^6181 ≤ 2909625830397^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350521861 10000000000 2909625830397 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055926233/2000000000 : ℝ)^8229 ≤ (42725939187521/100000000000000 : ℝ)^6181 := by
    have hnat : (1055926233 : ℕ)^8229*100000000000000^6181 ≤ 42725939187521^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055926233 2000000000 42725939187521 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055926093/2000000000 : ℝ)^8229 ≤ (10681482911433/25000000000000 : ℝ)^6181 := by
    have hnat : (1055926093 : ℕ)^8229*25000000000000^6181 ≤ 10681482911433^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055926093 2000000000 10681482911433 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2350521861/10000000000 : ℝ), (1055926233/2000000000 : ℝ), (1055926093/2000000000 : ℝ)] ![(2909625830397/20000000000000 : ℝ), (42725939187521/100000000000000 : ℝ), (10681482911433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2350521861/10000000000 : ℝ)|^8229 ≤ (2909625830397/20000000000000 : ℝ)^6181
        have hw : |(-2350521861/10000000000 : ℝ)|=(2350521861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055926233/2000000000 : ℝ)|^8229 ≤ (42725939187521/100000000000000 : ℝ)^6181
        have hw : |(1055926233/2000000000 : ℝ)|=(1055926233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055926093/2000000000 : ℝ)|^8229 ≤ (10681482911433/25000000000000 : ℝ)^6181
        have hw : |(1055926093/2000000000 : ℝ)|=(1055926093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682177079/5000000000 : ℝ)*x 0 + (-1119279063/5000000000 : ℝ)*x 1 + (5279631197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682177079/5000000000 : ℝ)^8229 ≤ (21820580747657/50000000000000 : ℝ)^6181 := by
    have hnat : (2682177079 : ℕ)^8229*50000000000000^6181 ≤ 21820580747657^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682177079 5000000000 21820580747657 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119279063/5000000000 : ℝ)^8229 ≤ (13632898963213/100000000000000 : ℝ)^6181 := by
    have hnat : (1119279063 : ℕ)^8229*100000000000000^6181 ≤ 13632898963213^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119279063 5000000000 13632898963213 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279631197/10000000000 : ℝ)^8229 ≤ (42725939532289/100000000000000 : ℝ)^6181 := by
    have hnat : (5279631197 : ℕ)^8229*100000000000000^6181 ≤ 42725939532289^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279631197 10000000000 42725939532289 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682177079/5000000000 : ℝ), (-1119279063/5000000000 : ℝ), (5279631197/10000000000 : ℝ)] ![(21820580747657/50000000000000 : ℝ), (13632898963213/100000000000000 : ℝ), (42725939532289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682177079/5000000000 : ℝ)|^8229 ≤ (21820580747657/50000000000000 : ℝ)^6181
        have hw : |(2682177079/5000000000 : ℝ)|=(2682177079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119279063/5000000000 : ℝ)|^8229 ≤ (13632898963213/100000000000000 : ℝ)^6181
        have hw : |(-1119279063/5000000000 : ℝ)|=(1119279063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279631197/10000000000 : ℝ)|^8229 ≤ (42725939532289/100000000000000 : ℝ)^6181
        have hw : |(5279631197/10000000000 : ℝ)|=(5279631197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364354611/10000000000 : ℝ)*x 0 + (65995381/125000000 : ℝ)*x 1 + (-2238558473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364354611/10000000000 : ℝ)^8229 ≤ (21820583200871/50000000000000 : ℝ)^6181 := by
    have hnat : (5364354611 : ℕ)^8229*50000000000000^6181 ≤ 21820583200871^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364354611 10000000000 21820583200871 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65995381/125000000 : ℝ)^8229 ≤ (21362965903671/50000000000000 : ℝ)^6181 := by
    have hnat : (65995381 : ℕ)^8229*50000000000000^6181 ≤ 21362965903671^6181*125000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65995381 125000000 21362965903671 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238558473/10000000000 : ℝ)^8229 ≤ (13632901776653/100000000000000 : ℝ)^6181 := by
    have hnat : (2238558473 : ℕ)^8229*100000000000000^6181 ≤ 13632901776653^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238558473 10000000000 13632901776653 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364354611/10000000000 : ℝ), (65995381/125000000 : ℝ), (-2238558473/10000000000 : ℝ)] ![(21820583200871/50000000000000 : ℝ), (21362965903671/50000000000000 : ℝ), (13632901776653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364354611/10000000000 : ℝ)|^8229 ≤ (21820583200871/50000000000000 : ℝ)^6181
        have hw : |(5364354611/10000000000 : ℝ)|=(5364354611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65995381/125000000 : ℝ)|^8229 ≤ (21362965903671/50000000000000 : ℝ)^6181
        have hw : |(65995381/125000000 : ℝ)|=(65995381/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238558473/10000000000 : ℝ)|^8229 ≤ (13632901776653/100000000000000 : ℝ)^6181
        have hw : |(-2238558473/10000000000 : ℝ)|=(2238558473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4270778723/10000000000 : ℝ)*x 0 + (1109128141/2500000000 : ℝ)*x 1 + (2218256003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270778723/10000000000 : ℝ)^8229 ≤ (8054156078971/25000000000000 : ℝ)^6181 := by
    have hnat : (4270778723 : ℕ)^8229*25000000000000^6181 ≤ 8054156078971^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270778723 10000000000 8054156078971 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109128141/2500000000 : ℝ)^8229 ≤ (16945845334961/50000000000000 : ℝ)^6181 := by
    have hnat : (1109128141 : ℕ)^8229*50000000000000^6181 ≤ 16945845334961^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109128141 2500000000 16945845334961 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218256003/5000000000 : ℝ)^8229 ≤ (132389394511/390625000000 : ℝ)^6181 := by
    have hnat : (2218256003 : ℕ)^8229*390625000000^6181 ≤ 132389394511^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218256003 5000000000 132389394511 390625000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270778723/10000000000 : ℝ), (1109128141/2500000000 : ℝ), (2218256003/5000000000 : ℝ)] ![(8054156078971/25000000000000 : ℝ), (16945845334961/50000000000000 : ℝ), (132389394511/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270778723/10000000000 : ℝ)|^8229 ≤ (8054156078971/25000000000000 : ℝ)^6181
        have hw : |(4270778723/10000000000 : ℝ)|=(4270778723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1109128141/2500000000 : ℝ)|^8229 ≤ (16945845334961/50000000000000 : ℝ)^6181
        have hw : |(1109128141/2500000000 : ℝ)|=(1109128141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2218256003/5000000000 : ℝ)|^8229 ≤ (132389394511/390625000000 : ℝ)^6181
        have hw : |(2218256003/5000000000 : ℝ)|=(2218256003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_8 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2295782853/10000000000 : ℝ)*x 0 + (162909349/312500000 : ℝ)*x 1 + (5387363319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295782853/10000000000 : ℝ)^8229 ≤ (14098824945757/100000000000000 : ℝ)^6181 := by
    have hnat : (2295782853 : ℕ)^8229*100000000000000^6181 ≤ 14098824945757^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295782853 10000000000 14098824945757 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162909349/312500000 : ℝ)^8229 ≤ (42010625192209/100000000000000 : ℝ)^6181 := by
    have hnat : (162909349 : ℕ)^8229*100000000000000^6181 ≤ 42010625192209^6181*312500000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162909349 312500000 42010625192209 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387363319/10000000000 : ℝ)^8229 ≤ (43890549847203/100000000000000 : ℝ)^6181 := by
    have hnat : (5387363319 : ℕ)^8229*100000000000000^6181 ≤ 43890549847203^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387363319 10000000000 43890549847203 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2295782853/10000000000 : ℝ), (162909349/312500000 : ℝ), (5387363319/10000000000 : ℝ)] ![(14098824945757/100000000000000 : ℝ), (42010625192209/100000000000000 : ℝ), (43890549847203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2295782853/10000000000 : ℝ)|^8229 ≤ (14098824945757/100000000000000 : ℝ)^6181
        have hw : |(-2295782853/10000000000 : ℝ)|=(2295782853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162909349/312500000 : ℝ)|^8229 ≤ (42010625192209/100000000000000 : ℝ)^6181
        have hw : |(162909349/312500000 : ℝ)|=(162909349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387363319/10000000000 : ℝ)|^8229 ≤ (43890549847203/100000000000000 : ℝ)^6181
        have hw : |(5387363319/10000000000 : ℝ)|=(5387363319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_9 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661006661/1250000000 : ℝ)*x 0 + (-2196473617/10000000000 : ℝ)*x 1 + (2693681557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661006661/1250000000 : ℝ)^8229 ≤ (42816702983469/100000000000000 : ℝ)^6181 := by
    have hnat : (661006661 : ℕ)^8229*100000000000000^6181 ≤ 42816702983469^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661006661 1250000000 42816702983469 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196473617/10000000000 : ℝ)^8229 ≤ (1329274937381/10000000000000 : ℝ)^6181 := by
    have hnat : (2196473617 : ℕ)^8229*10000000000000^6181 ≤ 1329274937381^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196473617 10000000000 1329274937381 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693681557/5000000000 : ℝ)^8229 ≤ (5486318452963/12500000000000 : ℝ)^6181 := by
    have hnat : (2693681557 : ℕ)^8229*12500000000000^6181 ≤ 5486318452963^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693681557 5000000000 5486318452963 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661006661/1250000000 : ℝ), (-2196473617/10000000000 : ℝ), (2693681557/5000000000 : ℝ)] ![(42816702983469/100000000000000 : ℝ), (1329274937381/10000000000000 : ℝ), (5486318452963/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661006661/1250000000 : ℝ)|^8229 ≤ (42816702983469/100000000000000 : ℝ)^6181
        have hw : |(661006661/1250000000 : ℝ)|=(661006661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196473617/10000000000 : ℝ)|^8229 ≤ (1329274937381/10000000000000 : ℝ)^6181
        have hw : |(-2196473617/10000000000 : ℝ)|=(2196473617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693681557/5000000000 : ℝ)|^8229 ≤ (5486318452963/12500000000000 : ℝ)^6181
        have hw : |(2693681557/5000000000 : ℝ)|=(2693681557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_10 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322013403/2500000000 : ℝ)*x 0 + (1346840811/2500000000 : ℝ)*x 1 + (-2196473009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322013403/2500000000 : ℝ)^8229 ≤ (10704176619021/25000000000000 : ℝ)^6181 := by
    have hnat : (1322013403 : ℕ)^8229*25000000000000^6181 ≤ 10704176619021^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322013403 2500000000 10704176619021 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346840811/2500000000 : ℝ)^8229 ≤ (171447457163/390625000000 : ℝ)^6181 := by
    have hnat : (1346840811 : ℕ)^8229*390625000000^6181 ≤ 171447457163^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346840811 2500000000 171447457163 390625000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196473009/10000000000 : ℝ)^8229 ≤ (1661593059389/12500000000000 : ℝ)^6181 := by
    have hnat : (2196473009 : ℕ)^8229*12500000000000^6181 ≤ 1661593059389^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196473009 10000000000 1661593059389 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322013403/2500000000 : ℝ), (1346840811/2500000000 : ℝ), (-2196473009/10000000000 : ℝ)] ![(10704176619021/25000000000000 : ℝ), (171447457163/390625000000 : ℝ), (1661593059389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322013403/2500000000 : ℝ)|^8229 ≤ (10704176619021/25000000000000 : ℝ)^6181
        have hw : |(1322013403/2500000000 : ℝ)|=(1322013403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346840811/2500000000 : ℝ)|^8229 ≤ (171447457163/390625000000 : ℝ)^6181
        have hw : |(1346840811/2500000000 : ℝ)|=(1346840811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196473009/10000000000 : ℝ)|^8229 ≤ (1661593059389/12500000000000 : ℝ)^6181
        have hw : |(-2196473009/10000000000 : ℝ)|=(2196473009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_11 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4509578887/10000000000 : ℝ)*x 0 + (1079248333/2500000000 : ℝ)*x 1 + (4316993491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509578887/10000000000 : ℝ)^8229 ≤ (8659206913707/25000000000000 : ℝ)^6181 := by
    have hnat : (4509578887 : ℕ)^8229*25000000000000^6181 ≤ 8659206913707^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509578887 10000000000 8659206913707 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079248333/2500000000 : ℝ)^8229 ≤ (32681585363477/100000000000000 : ℝ)^6181 := by
    have hnat : (1079248333 : ℕ)^8229*100000000000000^6181 ≤ 32681585363477^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079248333 2500000000 32681585363477 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316993491/10000000000 : ℝ)^8229 ≤ (32681586966011/100000000000000 : ℝ)^6181 := by
    have hnat : (4316993491 : ℕ)^8229*100000000000000^6181 ≤ 32681586966011^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316993491 10000000000 32681586966011 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509578887/10000000000 : ℝ), (1079248333/2500000000 : ℝ), (4316993491/10000000000 : ℝ)] ![(8659206913707/25000000000000 : ℝ), (32681585363477/100000000000000 : ℝ), (32681586966011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509578887/10000000000 : ℝ)|^8229 ≤ (8659206913707/25000000000000 : ℝ)^6181
        have hw : |(4509578887/10000000000 : ℝ)|=(4509578887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079248333/2500000000 : ℝ)|^8229 ≤ (32681585363477/100000000000000 : ℝ)^6181
        have hw : |(1079248333/2500000000 : ℝ)|=(1079248333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316993491/10000000000 : ℝ)|^8229 ≤ (32681586966011/100000000000000 : ℝ)^6181
        have hw : |(4316993491/10000000000 : ℝ)|=(4316993491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_12 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143253771/10000000000 : ℝ)*x 0 + (2721469841/5000000000 : ℝ)*x 1 + (5271646897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143253771/10000000000 : ℝ)^8229 ≤ (12865683965393/100000000000000 : ℝ)^6181 := by
    have hnat : (2143253771 : ℕ)^8229*100000000000000^6181 ≤ 12865683965393^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143253771 10000000000 12865683965393 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721469841/5000000000 : ℝ)^8229 ≤ (1779775105637/4000000000000 : ℝ)^6181 := by
    have hnat : (2721469841 : ℕ)^8229*4000000000000^6181 ≤ 1779775105637^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721469841 5000000000 1779775105637 4000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271646897/10000000000 : ℝ)^8229 ≤ (42639938365649/100000000000000 : ℝ)^6181 := by
    have hnat : (5271646897 : ℕ)^8229*100000000000000^6181 ≤ 42639938365649^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271646897 10000000000 42639938365649 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143253771/10000000000 : ℝ), (2721469841/5000000000 : ℝ), (5271646897/10000000000 : ℝ)] ![(12865683965393/100000000000000 : ℝ), (1779775105637/4000000000000 : ℝ), (42639938365649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143253771/10000000000 : ℝ)|^8229 ≤ (12865683965393/100000000000000 : ℝ)^6181
        have hw : |(-2143253771/10000000000 : ℝ)|=(2143253771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721469841/5000000000 : ℝ)|^8229 ≤ (1779775105637/4000000000000 : ℝ)^6181
        have hw : |(2721469841/5000000000 : ℝ)|=(2721469841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271646897/10000000000 : ℝ)|^8229 ≤ (42639938365649/100000000000000 : ℝ)^6181
        have hw : |(5271646897/10000000000 : ℝ)|=(5271646897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_13 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671250761/1250000000 : ℝ)*x 0 + (-2241613043/10000000000 : ℝ)*x 1 + (5271646903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671250761/1250000000 : ℝ)^8229 ≤ (43702388037513/100000000000000 : ℝ)^6181 := by
    have hnat : (671250761 : ℕ)^8229*100000000000000^6181 ≤ 43702388037513^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671250761 1250000000 43702388037513 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241613043/10000000000 : ℝ)^8229 ≤ (2731534702029/20000000000000 : ℝ)^6181 := by
    have hnat : (2241613043 : ℕ)^8229*20000000000000^6181 ≤ 2731534702029^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241613043 10000000000 2731534702029 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271646903/10000000000 : ℝ)^8229 ≤ (2131996921513/5000000000000 : ℝ)^6181 := by
    have hnat : (5271646903 : ℕ)^8229*5000000000000^6181 ≤ 2131996921513^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271646903 10000000000 2131996921513 5000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671250761/1250000000 : ℝ), (-2241613043/10000000000 : ℝ), (5271646903/10000000000 : ℝ)] ![(43702388037513/100000000000000 : ℝ), (2731534702029/20000000000000 : ℝ), (2131996921513/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671250761/1250000000 : ℝ)|^8229 ≤ (43702388037513/100000000000000 : ℝ)^6181
        have hw : |(671250761/1250000000 : ℝ)|=(671250761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241613043/10000000000 : ℝ)|^8229 ≤ (2731534702029/20000000000000 : ℝ)^6181
        have hw : |(-2241613043/10000000000 : ℝ)|=(2241613043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271646903/10000000000 : ℝ)|^8229 ≤ (2131996921513/5000000000000 : ℝ)^6181
        have hw : |(5271646903/10000000000 : ℝ)|=(5271646903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_14 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685003093/5000000000 : ℝ)*x 0 + (527164687/1000000000 : ℝ)*x 1 + (-560403239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685003093/5000000000 : ℝ)^8229 ≤ (21851194549659/50000000000000 : ℝ)^6181 := by
    have hnat : (2685003093 : ℕ)^8229*50000000000000^6181 ≤ 21851194549659^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685003093 5000000000 21851194549659 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527164687/1000000000 : ℝ)^8229 ≤ (42639938074897/100000000000000 : ℝ)^6181 := by
    have hnat : (527164687 : ℕ)^8229*100000000000000^6181 ≤ 42639938074897^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527164687 1000000000 42639938074897 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560403239/2500000000 : ℝ)^8229 ≤ (13657672804439/100000000000000 : ℝ)^6181 := by
    have hnat : (560403239 : ℕ)^8229*100000000000000^6181 ≤ 13657672804439^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560403239 2500000000 13657672804439 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685003093/5000000000 : ℝ), (527164687/1000000000 : ℝ), (-560403239/2500000000 : ℝ)] ![(21851194549659/50000000000000 : ℝ), (42639938074897/100000000000000 : ℝ), (13657672804439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685003093/5000000000 : ℝ)|^8229 ≤ (21851194549659/50000000000000 : ℝ)^6181
        have hw : |(2685003093/5000000000 : ℝ)|=(2685003093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527164687/1000000000 : ℝ)|^8229 ≤ (42639938074897/100000000000000 : ℝ)^6181
        have hw : |(527164687/1000000000 : ℝ)|=(527164687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560403239/2500000000 : ℝ)|^8229 ≤ (13657672804439/100000000000000 : ℝ)^6181
        have hw : |(-560403239/2500000000 : ℝ)|=(560403239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_box_15 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2126415273/5000000000 : ℝ)*x 0 + (4445364739/10000000000 : ℝ)*x 1 + (277835301/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126415273/5000000000 : ℝ)^8229 ≤ (2002281080957/6250000000000 : ℝ)^6181 := by
    have hnat : (2126415273 : ℕ)^8229*6250000000000^6181 ≤ 2002281080957^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126415273 5000000000 2002281080957 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4445364739/10000000000 : ℝ)^8229 ≤ (8495437737877/25000000000000 : ℝ)^6181 := by
    have hnat : (4445364739 : ℕ)^8229*25000000000000^6181 ≤ 8495437737877^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445364739 10000000000 8495437737877 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277835301/625000000 : ℝ)^8229 ≤ (33981751735149/100000000000000 : ℝ)^6181 := by
    have hnat : (277835301 : ℕ)^8229*100000000000000^6181 ≤ 33981751735149^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277835301 625000000 33981751735149 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126415273/5000000000 : ℝ), (4445364739/10000000000 : ℝ), (277835301/625000000 : ℝ)] ![(2002281080957/6250000000000 : ℝ), (8495437737877/25000000000000 : ℝ), (33981751735149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126415273/5000000000 : ℝ)|^8229 ≤ (2002281080957/6250000000000 : ℝ)^6181
        have hw : |(2126415273/5000000000 : ℝ)|=(2126415273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4445364739/10000000000 : ℝ)|^8229 ≤ (8495437737877/25000000000000 : ℝ)^6181
        have hw : |(4445364739/10000000000 : ℝ)|=(4445364739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277835301/625000000 : ℝ)|^8229 ≤ (33981751735149/100000000000000 : ℝ)^6181
        have hw : |(277835301/625000000 : ℝ)|=(277835301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59219/100000 : ℝ) ∧ (79477/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20721/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1121/10000 : ℝ) ^ (2057/512 : ℝ) ≤ (303910912620729/2000000000000000000 : ℝ) := by
    have hpowers : (1121/10000 : ℝ)^2057 ≤ (303910912620729/2000000000000000000 : ℝ)^512 := by
      have hnat : (1121 : ℕ)^2057*2000000000000000000^512 ≤ 303910912620729^512*10000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 10000 303910912620729 2000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/10000 : ℝ)) (X := (303910912620729/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13983/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (9232571838351479/25000000000000000000 : ℝ) := by
    have hpowers : (13983/100000 : ℝ)^2057 ≤ (9232571838351479/25000000000000000000 : ℝ)^512 := by
      have hnat : (13983 : ℕ)^2057*25000000000000000000^512 ≤ 9232571838351479^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13983 100000 9232571838351479 25000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13983/100000 : ℝ)) (X := (9232571838351479/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000303910912620729/1000000000000000000 : ℝ) ≤ (10000756366704301/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (1000303910912620729/1000000000000000000 : ℝ)^512 ≤ (10000756366704301/10000000000000000 : ℝ)^2057 := by
      have hnat : (1000303910912620729 : ℕ)^512*10000000000000000^2057 ≤ 10000756366704301^2057*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000303910912620729 1000000000000000000 10000756366704301 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000756366704301/10000000000000000 : ℝ)) (X := (1000303910912620729/1000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026062916492221183/50000000000000000000 : ℝ) ≤ (1250162148782401/1250000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (50026062916492221183/50000000000000000000 : ℝ)^512 ≤ (1250162148782401/1250000000000000 : ℝ)^2057 := by
      have hnat : (50026062916492221183 : ℕ)^512*1250000000000000^2057 ≤ 1250162148782401^2057*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026062916492221183 50000000000000000000 1250162148782401 1250000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250162148782401/1250000000000000 : ℝ)) (X := (50026062916492221183/50000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509232571838351479/12500000000000000000 : ℝ) ≤ (2000367602762823/2000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (12509232571838351479/12500000000000000000 : ℝ)^512 ≤ (2000367602762823/2000000000000000 : ℝ)^2057 := by
      have hnat : (12509232571838351479 : ℕ)^512*2000000000000000^2057 ≤ 2000367602762823^2057*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509232571838351479 12500000000000000000 2000367602762823 2000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000367602762823/2000000000000000 : ℝ)) (X := (12509232571838351479/12500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(303910912620729/2000000000000000000 : ℝ) ≤ ((469830036284237487/470000000000000000 : ℝ)+2*(540823554907/277300000000000 : ℝ)*(1121/10000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (469830036284237487/470000000000000000 : ℝ)+2*(540823554907/277300000000000 : ℝ)*(1121/10000 : ℝ)=(10000756366704301/10000000000000000 : ℝ) by norm_num, show 1+2*(303910912620729/2000000000000000000 : ℝ)=(1000303910912620729/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9232571838351479/25000000000000000000 : ℝ)+(303910912620729/2000000000000000000 : ℝ) ≤ ((469830036284237487/470000000000000000 : ℝ)+(540823554907/277300000000000 : ℝ)*((13983/100000 : ℝ)+(1121/10000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (469830036284237487/470000000000000000 : ℝ)+(540823554907/277300000000000 : ℝ)*((13983/100000 : ℝ)+(1121/10000 : ℝ))=(1250162148782401/1250000000000000 : ℝ) by norm_num, show 1+(9232571838351479/25000000000000000000 : ℝ)+(303910912620729/2000000000000000000 : ℝ)=(50026062916492221183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9232571838351479/25000000000000000000 : ℝ) ≤ ((469830036284237487/470000000000000000 : ℝ)+2*(540823554907/277300000000000 : ℝ)*(13983/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (469830036284237487/470000000000000000 : ℝ)+2*(540823554907/277300000000000 : ℝ)*(13983/100000 : ℝ)=(2000367602762823/2000000000000000 : ℝ) by norm_num, show 1+2*(9232571838351479/25000000000000000000 : ℝ)=(12509232571838351479/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (469830036284237487/470000000000000000 : ℝ)*(X 1 0+X 2 0)+(540823554907/277300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (469830036284237487/470000000000000000 : ℝ)) (alpha := (540823554907/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (469830036284237487/470000000000000000 : ℝ)*(X 0 1+X 2 1)+(540823554907/277300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (469830036284237487/470000000000000000 : ℝ)) (alpha := (540823554907/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (469830036284237487/470000000000000000 : ℝ)*(X 0 2+X 1 2)+(540823554907/277300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (13983/100000 : ℝ)) (c := (469830036284237487/470000000000000000 : ℝ)) (alpha := (540823554907/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-522031633/2500000000 : ℝ)*X 0 0+(5377767429/10000000000 : ℝ)*X 0 1+(672220883/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294853321/10000000000 : ℝ)*X 1 0+(-2200286449/10000000000 : ℝ)*X 1 1+(336110467/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294853713/10000000000 : ℝ)*X 2 0+(2688883501/5000000000 : ℝ)*X 2 1+(-440057311/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4488558739/10000000000 : ℝ)*X 0 0+(2163822063/5000000000 : ℝ)*X 0 1+(4327643841/10000000000 : ℝ)*X 0 2+(4488558739/10000000000 : ℝ)*X 1 0+(2163822063/5000000000 : ℝ)*X 1 1+(4327643841/10000000000 : ℝ)*X 1 2+(4488558739/10000000000 : ℝ)*X 2 0+(2163822063/5000000000 : ℝ)*X 2 1+(4327643841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2350521861/10000000000 : ℝ)*X 0 0+(1055926233/2000000000 : ℝ)*X 0 1+(1055926093/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682177079/5000000000 : ℝ)*X 1 0+(-1119279063/5000000000 : ℝ)*X 1 1+(5279631197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364354611/10000000000 : ℝ)*X 2 0+(65995381/125000000 : ℝ)*X 2 1+(-2238558473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4270778723/10000000000 : ℝ)*X 0 0+(1109128141/2500000000 : ℝ)*X 0 1+(2218256003/5000000000 : ℝ)*X 0 2+(4270778723/10000000000 : ℝ)*X 1 0+(1109128141/2500000000 : ℝ)*X 1 1+(2218256003/5000000000 : ℝ)*X 1 2+(4270778723/10000000000 : ℝ)*X 2 0+(1109128141/2500000000 : ℝ)*X 2 1+(2218256003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2295782853/10000000000 : ℝ)*X 0 0+(162909349/312500000 : ℝ)*X 0 1+(5387363319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661006661/1250000000 : ℝ)*X 1 0+(-2196473617/10000000000 : ℝ)*X 1 1+(2693681557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322013403/2500000000 : ℝ)*X 2 0+(1346840811/2500000000 : ℝ)*X 2 1+(-2196473009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4509578887/10000000000 : ℝ)*X 0 0+(1079248333/2500000000 : ℝ)*X 0 1+(4316993491/10000000000 : ℝ)*X 0 2+(4509578887/10000000000 : ℝ)*X 1 0+(1079248333/2500000000 : ℝ)*X 1 1+(4316993491/10000000000 : ℝ)*X 1 2+(4509578887/10000000000 : ℝ)*X 2 0+(1079248333/2500000000 : ℝ)*X 2 1+(4316993491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2143253771/10000000000 : ℝ)*X 0 0+(2721469841/5000000000 : ℝ)*X 0 1+(5271646897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671250761/1250000000 : ℝ)*X 1 0+(-2241613043/10000000000 : ℝ)*X 1 1+(5271646903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2685003093/5000000000 : ℝ)*X 2 0+(527164687/1000000000 : ℝ)*X 2 1+(-560403239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2126415273/5000000000 : ℝ)*X 0 0+(4445364739/10000000000 : ℝ)*X 0 1+(277835301/625000000 : ℝ)*X 0 2+(2126415273/5000000000 : ℝ)*X 1 0+(4445364739/10000000000 : ℝ)*X 1 1+(277835301/625000000 : ℝ)*X 1 2+(2126415273/5000000000 : ℝ)*X 2 0+(4445364739/10000000000 : ℝ)*X 2 1+(277835301/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-53918162417984279495991962585589/86656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93560867/100000000000000 : ℝ)*(lower0) + (27758343/100000000000000 : ℝ)*(upper3) + (74058099/100000000000000 : ℝ)*(lower5) + (478909574977861/12500000000000 : ℝ)*(major0) + (478909574977861/12500000000000 : ℝ)*(major1) + (478909574977861/12500000000000 : ℝ)*(major2) + (2802867159/12500000000000 : ℝ)*(sp2) + (5084205889173221/100000000000000 : ℝ)*(sp4) + (5084096324683413/100000000000000 : ℝ)*(sp5) + (158881427165943/3125000000000 : ℝ)*(sp6) + (1299513218610061/50000000000000 : ℝ)*(sp7) + (22203074227/100000000000000 : ℝ)*(sp8) + (32941891009/25000000000000 : ℝ)*(sp13) + (38917772557/100000000000000 : ℝ)*(sp15) + (2599065354992679/100000000000000 : ℝ)*(f.failure) + (5084228092247449/100000000000000 : ℝ)*(f.sum) + (2338275774553/1733125000000000000000000000 : ℝ)*base66 + (17414293667985943113/346625000000000000000000000000000 : ℝ)*base67 + (2844799017802193113/346625000000000000000000000000000 : ℝ)*base69 + (276506616859193113/346625000000000000000000000000000 : ℝ)*base71 + (382334111214509/13865000000000000000000000000 : ℝ)*base74 + (1948663788465681887/346625000000000000000000000000000 : ℝ)*base76 + (1656046369527943113/346625000000000000000000000000000 : ℝ)*base77 + (9937492789988568113/346625000000000000000000000000000 : ℝ)*base79 + (15664437946931/3466250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (22021343/10000000000000000000000 : ℝ)*base90 + (22021343/10000000000000000000000 : ℝ)*base92 + (22021343/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59219/100000 : ℝ) ≤ (821100817705788271692767874909561/1386500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140298537/100000000000000 : ℝ)*(lower1) + (416933/12500000000000 : ℝ)*(lower2) + (4422959/2500000000000 : ℝ)*(upper4) + (129260903/50000000000000 : ℝ)*(lower5) + (3893710427365587/100000000000000 : ℝ)*(major0) + (3893710427365587/100000000000000 : ℝ)*(major1) + (3893710427365587/100000000000000 : ℝ)*(major2) + (5126261202616033/100000000000000 : ℝ)*(sp0) + (5126254186564091/100000000000000 : ℝ)*(sp1) + (5126257164317979/100000000000000 : ℝ)*(sp2) + (132069650364751/5000000000000 : ℝ)*(sp3) + (3508025971/50000000000000 : ℝ)*(sp5) + (4038298053/100000000000000 : ℝ)*(sp6) + (26271753499/100000000000000 : ℝ)*(sp7) + (66035481976213/2500000000000 : ℝ)*(f.failure) + (5126261202616033/100000000000000 : ℝ)*(f.sum) + (13170348807693/1733125000000000000000000000 : ℝ)*base65 + (14245448872462332271/2773000000000000000000000000000000 : ℝ)*base67 + (11689810996013332271/2773000000000000000000000000000000 : ℝ)*base69 + (17793642433919332271/2773000000000000000000000000000000 : ℝ)*base71 + (10081432555021/3466250000000000000000000000 : ℝ)*base73 + (17588133362991332271/2773000000000000000000000000000000 : ℝ)*base75 + (4479617116320332271/2773000000000000000000000000000000 : ℝ)*base77 + (27044520869169332271/2773000000000000000000000000000000 : ℝ)*base79 + (43085905164409/13865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1991779/250000000000000000000 : ℝ)*base89 + (1991779/250000000000000000000 : ℝ)*base91 + (1991779/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79477/100000 : ℝ) ≤ (550993769081537710212946098879909/693250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89116843/50000000000000 : ℝ)*(upper0) + (110018597/100000000000000 : ℝ)*(lower3) + (18896819/5000000000000 : ℝ)*(upper4) + (2181008786628903/50000000000000 : ℝ)*(major0) + (2181008786628903/50000000000000 : ℝ)*(major1) + (2181008786628903/50000000000000 : ℝ)*(major2) + (100571574173/100000000000000 : ℝ)*(sp1) + (382935764863/100000000000000 : ℝ)*(sp2) + (138813307231/100000000000000 : ℝ)*(sp3) + (9665031247/100000000000000 : ℝ)*(sp4) + (2869211125227863/50000000000000 : ℝ)*(sp8) + (7172914179891/125000000000 : ℝ)*(sp9) + (573804897972211/10000000000000 : ℝ)*(sp10) + (1479485574191111/50000000000000 : ℝ)*(sp11) + (2959109961689453/100000000000000 : ℝ)*(f.failure) + (5738431915486973/100000000000000 : ℝ)*(f.sum) + (15985898715357/3466250000000000000000000000 : ℝ)*base66 + (24241287202024518899/1386500000000000000000000000000000 : ℝ)*base67 + (18221356282976018899/1386500000000000000000000000000000 : ℝ)*base69 + (5839123981135018899/1386500000000000000000000000000000 : ℝ)*base71 + (125042599271003/13865000000000000000000000000 : ℝ)*base74 + (9315720636170518899/1386500000000000000000000000000000 : ℝ)*base75 + (12826969309266018899/1386500000000000000000000000000000 : ℝ)*base77 + (13940802834205018899/1386500000000000000000000000000000 : ℝ)*base79 + (12541499479993/3466250000000000000000000000 : ℝ)*base81 + (19881301/10000000000000000000000 : ℝ)*base90 + (19881301/10000000000000000000000 : ℝ)*base92 + (19881301/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20721/25000 : ℝ) ≤ (-2434632273405378455890722986823/2937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5708423/12500000000000 : ℝ)*(lower1) + (67224979/100000000000000 : ℝ)*(lower2) + (708503/3125000000000 : ℝ)*(upper5) + (549546683961319/12500000000000 : ℝ)*(major0) + (549546683961319/12500000000000 : ℝ)*(major1) + (549546683961319/12500000000000 : ℝ)*(major2) + (90810909/12500000000000 : ℝ)*(sp0) + (780815803/1250000000000 : ℝ)*(sp5) + (22376007363/50000000000000 : ℝ)*(sp6) + (17036951493/50000000000000 : ℝ)*(sp7) + (5837956898427419/100000000000000 : ℝ)*(sp12) + (5837895159650451/100000000000000 : ℝ)*(sp13) + (1167582574579993/20000000000000 : ℝ)*(sp14) + (9319944617041/312500000000 : ℝ)*(sp15) + (1491208175678053/50000000000000 : ℝ)*(f.failure) + (5837957624914691/100000000000000 : ℝ)*(f.sum) + (240162672665739/13865000000000000000000000000 : ℝ)*base65 + (5636235507942294173/346625000000000000000000000000000 : ℝ)*base68 + (8735582202624919173/346625000000000000000000000000000 : ℝ)*base70 + (4505326306548294173/346625000000000000000000000000000 : ℝ)*base72 + (96256693720049/13865000000000000000000000000 : ℝ)*base73 + (5131139845373169173/346625000000000000000000000000000 : ℝ)*base76 + (1223664333393794173/346625000000000000000000000000000 : ℝ)*base78 + (7680353700246294173/346625000000000000000000000000000 : ℝ)*base80 + (6161413056447/6932500000000000000000000000 : ℝ)*base81 + (70592499/5000000000000000000000 : ℝ)*base89 + (70592499/5000000000000000000000 : ℝ)*base91 + (70592499/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (79477/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20721/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1036_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1036_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (79477/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20721/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1036_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1036_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (79477/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20721/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
