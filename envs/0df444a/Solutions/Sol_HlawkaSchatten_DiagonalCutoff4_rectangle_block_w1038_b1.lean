-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:44:32.75899+00:00
-- url     : https://prove2.me/submissions/e4b1d90c-acbd-48d6-91ef-8735f6f81c5d

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
theorem support_rectangle_w1038_s3_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106248361/5000000000 : ℝ)*x 0 + (5440849753/10000000000 : ℝ)*x 1 + (1044254877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106248361/5000000000 : ℝ)^8231 ≤ (536966982843/4000000000000 : ℝ)^6183 := by
    have hnat : (1106248361 : ℕ)^8231*4000000000000^6183 ≤ 536966982843^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106248361 5000000000 536966982843 4000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440849753/10000000000 : ℝ)^8231 ≤ (5559316865679/12500000000000 : ℝ)^6183 := by
    have hnat : (5440849753 : ℕ)^8231*12500000000000^6183 ≤ 5559316865679^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440849753 10000000000 5559316865679 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044254877/2000000000 : ℝ)^8231 ≤ (10525322622247/25000000000000 : ℝ)^6183 := by
    have hnat : (1044254877 : ℕ)^8231*25000000000000^6183 ≤ 10525322622247^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044254877 2000000000 10525322622247 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106248361/5000000000 : ℝ), (5440849753/10000000000 : ℝ), (1044254877/2000000000 : ℝ)] ![(536966982843/4000000000000 : ℝ), (5559316865679/12500000000000 : ℝ), (10525322622247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106248361/5000000000 : ℝ)|^8231 ≤ (536966982843/4000000000000 : ℝ)^6183
        have hw : |(-1106248361/5000000000 : ℝ)|=(1106248361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440849753/10000000000 : ℝ)|^8231 ≤ (5559316865679/12500000000000 : ℝ)^6183
        have hw : |(5440849753/10000000000 : ℝ)|=(5440849753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044254877/2000000000 : ℝ)|^8231 ≤ (10525322622247/25000000000000 : ℝ)^6183
        have hw : |(1044254877/2000000000 : ℝ)|=(1044254877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2678208141/5000000000 : ℝ)*x 0 + (-2325017163/10000000000 : ℝ)*x 1 + (5221274211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678208141/5000000000 : ℝ)^8231 ≤ (21779061037483/50000000000000 : ℝ)^6183 := by
    have hnat : (2678208141 : ℕ)^8231*50000000000000^6183 ≤ 21779061037483^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678208141 5000000000 21779061037483 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2325017163/10000000000 : ℝ)^8231 ≤ (7170294646883/50000000000000 : ℝ)^6183 := by
    have hnat : (2325017163 : ℕ)^8231*50000000000000^6183 ≤ 7170294646883^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325017163 10000000000 7170294646883 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221274211/10000000000 : ℝ)^8231 ≤ (21050644310613/50000000000000 : ℝ)^6183 := by
    have hnat : (5221274211 : ℕ)^8231*50000000000000^6183 ≤ 21050644310613^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221274211 10000000000 21050644310613 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678208141/5000000000 : ℝ), (-2325017163/10000000000 : ℝ), (5221274211/10000000000 : ℝ)] ![(21779061037483/50000000000000 : ℝ), (7170294646883/50000000000000 : ℝ), (21050644310613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678208141/5000000000 : ℝ)|^8231 ≤ (21779061037483/50000000000000 : ℝ)^6183
        have hw : |(2678208141/5000000000 : ℝ)|=(2678208141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2325017163/10000000000 : ℝ)|^8231 ≤ (7170294646883/50000000000000 : ℝ)^6183
        have hw : |(-2325017163/10000000000 : ℝ)|=(2325017163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221274211/10000000000 : ℝ)|^8231 ≤ (21050644310613/50000000000000 : ℝ)^6183
        have hw : |(5221274211/10000000000 : ℝ)|=(5221274211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334776011/625000000 : ℝ)*x 0 + (2610637033/5000000000 : ℝ)*x 1 + (-2325017491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334776011/625000000 : ℝ)^8231 ≤ (21779060463731/50000000000000 : ℝ)^6183 := by
    have hnat : (334776011 : ℕ)^8231*50000000000000^6183 ≤ 21779060463731^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334776011 625000000 21779060463731 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610637033/5000000000 : ℝ)^8231 ≤ (21050643532379/50000000000000 : ℝ)^6183 := by
    have hnat : (2610637033 : ℕ)^8231*50000000000000^6183 ≤ 21050643532379^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610637033 5000000000 21050643532379 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2325017491/10000000000 : ℝ)^8231 ≤ (7170295993481/50000000000000 : ℝ)^6183 := by
    have hnat : (2325017491 : ℕ)^8231*50000000000000^6183 ≤ 7170295993481^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325017491 10000000000 7170295993481 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334776011/625000000 : ℝ), (2610637033/5000000000 : ℝ), (-2325017491/10000000000 : ℝ)] ![(21779060463731/50000000000000 : ℝ), (21050643532379/50000000000000 : ℝ), (7170295993481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334776011/625000000 : ℝ)|^8231 ≤ (21779060463731/50000000000000 : ℝ)^6183
        have hw : |(334776011/625000000 : ℝ)|=(334776011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610637033/5000000000 : ℝ)|^8231 ≤ (21050643532379/50000000000000 : ℝ)^6183
        have hw : |(2610637033/5000000000 : ℝ)|=(2610637033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2325017491/10000000000 : ℝ)|^8231 ≤ (7170295993481/50000000000000 : ℝ)^6183
        have hw : |(-2325017491/10000000000 : ℝ)|=(2325017491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376503267/10000000000 : ℝ)*x 0 + (3256137/7812500 : ℝ)*x 1 + (4595803061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376503267/10000000000 : ℝ)^8231 ≤ (16642844586291/50000000000000 : ℝ)^6183 := by
    have hnat : (4376503267 : ℕ)^8231*50000000000000^6183 ≤ 16642844586291^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376503267 10000000000 16642844586291 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3256137/7812500 : ℝ)^8231 ≤ (7797511234627/25000000000000 : ℝ)^6183 := by
    have hnat : (3256137 : ℕ)^8231*25000000000000^6183 ≤ 7797511234627^6183*7812500^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3256137 7812500 7797511234627 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4595803061/10000000000 : ℝ)^8231 ≤ (4440533234293/12500000000000 : ℝ)^6183 := by
    have hnat : (4595803061 : ℕ)^8231*12500000000000^6183 ≤ 4440533234293^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595803061 10000000000 4440533234293 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376503267/10000000000 : ℝ), (3256137/7812500 : ℝ), (4595803061/10000000000 : ℝ)] ![(16642844586291/50000000000000 : ℝ), (7797511234627/25000000000000 : ℝ), (4440533234293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376503267/10000000000 : ℝ)|^8231 ≤ (16642844586291/50000000000000 : ℝ)^6183
        have hw : |(4376503267/10000000000 : ℝ)|=(4376503267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3256137/7812500 : ℝ)|^8231 ≤ (7797511234627/25000000000000 : ℝ)^6183
        have hw : |(3256137/7812500 : ℝ)|=(3256137/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4595803061/10000000000 : ℝ)|^8231 ≤ (4440533234293/12500000000000 : ℝ)^6183
        have hw : |(4595803061/10000000000 : ℝ)|=(4595803061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106260429/5000000000 : ℝ)*x 0 + (1305548303/2500000000 : ℝ)*x 1 + (543992541/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106260429/5000000000 : ℝ)^8231 ≤ (1678046190199/12500000000000 : ℝ)^6183 := by
    have hnat : (1106260429 : ℕ)^8231*12500000000000^6183 ≤ 1678046190199^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106260429 5000000000 1678046190199 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305548303/2500000000 : ℝ)^8231 ≤ (10527788426859/25000000000000 : ℝ)^6183 := by
    have hnat : (1305548303 : ℕ)^8231*25000000000000^6183 ≤ 10527788426859^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305548303 2500000000 10527788426859 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543992541/1000000000 : ℝ)^8231 ≤ (44464476755379/100000000000000 : ℝ)^6183 := by
    have hnat : (543992541 : ℕ)^8231*100000000000000^6183 ≤ 44464476755379^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543992541 1000000000 44464476755379 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106260429/5000000000 : ℝ), (1305548303/2500000000 : ℝ), (543992541/1000000000 : ℝ)] ![(1678046190199/12500000000000 : ℝ), (10527788426859/25000000000000 : ℝ), (44464476755379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106260429/5000000000 : ℝ)|^8231 ≤ (1678046190199/12500000000000 : ℝ)^6183
        have hw : |(-1106260429/5000000000 : ℝ)|=(1106260429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305548303/2500000000 : ℝ)|^8231 ≤ (10527788426859/25000000000000 : ℝ)^6183
        have hw : |(1305548303/2500000000 : ℝ)|=(1305548303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543992541/1000000000 : ℝ)|^8231 ≤ (44464476755379/100000000000000 : ℝ)^6183
        have hw : |(543992541/1000000000 : ℝ)|=(543992541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301227641/10000000000 : ℝ)*x 0 + (-2106365203/10000000000 : ℝ)*x 1 + (2719962963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301227641/10000000000 : ℝ)^8231 ≤ (10740424740947/25000000000000 : ℝ)^6183 := by
    have hnat : (5301227641 : ℕ)^8231*25000000000000^6183 ≤ 10740424740947^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301227641 10000000000 10740424740947 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106365203/10000000000 : ℝ)^8231 ≤ (12573818655979/100000000000000 : ℝ)^6183 := by
    have hnat : (2106365203 : ℕ)^8231*100000000000000^6183 ≤ 12573818655979^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106365203 10000000000 12573818655979 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719962963/5000000000 : ℝ)^8231 ≤ (44464482370037/100000000000000 : ℝ)^6183 := by
    have hnat : (2719962963 : ℕ)^8231*100000000000000^6183 ≤ 44464482370037^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719962963 5000000000 44464482370037 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301227641/10000000000 : ℝ), (-2106365203/10000000000 : ℝ), (2719962963/5000000000 : ℝ)] ![(10740424740947/25000000000000 : ℝ), (12573818655979/100000000000000 : ℝ), (44464482370037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301227641/10000000000 : ℝ)|^8231 ≤ (10740424740947/25000000000000 : ℝ)^6183
        have hw : |(5301227641/10000000000 : ℝ)|=(5301227641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106365203/10000000000 : ℝ)|^8231 ≤ (12573818655979/100000000000000 : ℝ)^6183
        have hw : |(-2106365203/10000000000 : ℝ)|=(2106365203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719962963/5000000000 : ℝ)|^8231 ≤ (44464482370037/100000000000000 : ℝ)^6183
        have hw : |(2719962963/5000000000 : ℝ)|=(2719962963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2650613757/5000000000 : ℝ)*x 0 + (5439925681/10000000000 : ℝ)*x 1 + (-2106365709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650613757/5000000000 : ℝ)^8231 ≤ (42961697593657/100000000000000 : ℝ)^6183 := by
    have hnat : (2650613757 : ℕ)^8231*100000000000000^6183 ≤ 42961697593657^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650613757 5000000000 42961697593657 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439925681/10000000000 : ℝ)^8231 ≤ (44464479704163/100000000000000 : ℝ)^6183 := by
    have hnat : (5439925681 : ℕ)^8231*100000000000000^6183 ≤ 44464479704163^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439925681 10000000000 44464479704163 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106365709/10000000000 : ℝ)^8231 ≤ (12573822677009/100000000000000 : ℝ)^6183 := by
    have hnat : (2106365709 : ℕ)^8231*100000000000000^6183 ≤ 12573822677009^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106365709 10000000000 12573822677009 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650613757/5000000000 : ℝ), (5439925681/10000000000 : ℝ), (-2106365709/10000000000 : ℝ)] ![(42961697593657/100000000000000 : ℝ), (44464479704163/100000000000000 : ℝ), (12573822677009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650613757/5000000000 : ℝ)|^8231 ≤ (42961697593657/100000000000000 : ℝ)^6183
        have hw : |(2650613757/5000000000 : ℝ)|=(2650613757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439925681/10000000000 : ℝ)|^8231 ≤ (44464479704163/100000000000000 : ℝ)^6183
        have hw : |(5439925681/10000000000 : ℝ)|=(5439925681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106365709/10000000000 : ℝ)|^8231 ≤ (12573822677009/100000000000000 : ℝ)^6183
        have hw : |(-2106365709/10000000000 : ℝ)|=(2106365709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s3_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875310061/2000000000 : ℝ)*x 0 + (4594012597/10000000000 : ℝ)*x 1 + (2084828343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875310061/2000000000 : ℝ)^8231 ≤ (33286165420699/100000000000000 : ℝ)^6183 := by
    have hnat : (875310061 : ℕ)^8231*100000000000000^6183 ≤ 33286165420699^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875310061 2000000000 33286165420699 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4594012597/10000000000 : ℝ)^8231 ≤ (8876460779317/25000000000000 : ℝ)^6183 := by
    have hnat : (4594012597 : ℕ)^8231*25000000000000^6183 ≤ 8876460779317^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594012597 10000000000 8876460779317 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084828343/5000000000 : ℝ)^8231 ≤ (31207991453093/100000000000000 : ℝ)^6183 := by
    have hnat : (2084828343 : ℕ)^8231*100000000000000^6183 ≤ 31207991453093^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084828343 5000000000 31207991453093 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875310061/2000000000 : ℝ), (4594012597/10000000000 : ℝ), (2084828343/5000000000 : ℝ)] ![(33286165420699/100000000000000 : ℝ), (8876460779317/25000000000000 : ℝ), (31207991453093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875310061/2000000000 : ℝ)|^8231 ≤ (33286165420699/100000000000000 : ℝ)^6183
        have hw : |(875310061/2000000000 : ℝ)|=(875310061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4594012597/10000000000 : ℝ)|^8231 ≤ (8876460779317/25000000000000 : ℝ)^6183
        have hw : |(4594012597/10000000000 : ℝ)|=(4594012597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084828343/5000000000 : ℝ)|^8231 ≤ (31207991453093/100000000000000 : ℝ)^6183
        have hw : |(2084828343/5000000000 : ℝ)|=(2084828343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5151/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4287/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4287/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4287/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4287/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4287/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4287/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4287/50000 : ℝ) ^ (4115/1024 : ℝ) ≤ (206537759182939/4000000000000000000 : ℝ) := by
    have hpowers : (4287/50000 : ℝ)^4115 ≤ (206537759182939/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4287 : ℕ)^4115*4000000000000000000^1024 ≤ 206537759182939^1024*50000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4287 50000 206537759182939 4000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4287/50000 : ℝ)) (X := (206537759182939/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16833/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (77676162672658383/100000000000000000000 : ℝ) := by
    have hpowers : (16833/100000 : ℝ)^4115 ≤ (77676162672658383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16833 : ℕ)^4115*100000000000000000000^1024 ≤ 77676162672658383^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16833 100000 77676162672658383 100000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16833/100000 : ℝ)) (X := (77676162672658383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000206537759182939/2000000000000000000 : ℝ) ≤ (312508030318309/312500000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (2000206537759182939/2000000000000000000 : ℝ)^1024 ≤ (312508030318309/312500000000000 : ℝ)^4115 := by
      have hnat : (2000206537759182939 : ℕ)^1024*312500000000000^4115 ≤ 312508030318309^4115*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000206537759182939 2000000000000000000 312508030318309 312500000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508030318309/312500000000000 : ℝ)) (X := (2000206537759182939/2000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50041419803326115929/50000000000000000000 : ℝ) ≤ (1000206078682361/1000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50041419803326115929/50000000000000000000 : ℝ)^1024 ≤ (1000206078682361/1000000000000000 : ℝ)^4115 := by
      have hnat : (50041419803326115929 : ℕ)^1024*1000000000000000^4115 ≤ 1000206078682361^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041419803326115929 50000000000000000000 1000206078682361 1000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000206078682361/1000000000000000 : ℝ)) (X := (50041419803326115929/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50077676162672658383/50000000000000000000 : ℝ) ≤ (2500966150865333/2500000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50077676162672658383/50000000000000000000 : ℝ)^1024 ≤ (2500966150865333/2500000000000000 : ℝ)^4115 := by
      have hnat : (50077676162672658383 : ℕ)^1024*2500000000000000^4115 ≤ 2500966150865333^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077676162672658383 50000000000000000000 2500966150865333 2500000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500966150865333/2500000000000000 : ℝ)) (X := (50077676162672658383/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(206537759182939/4000000000000000000 : ℝ) ≤ ((3440049602877566339/3441250000000000000 : ℝ)+2*(300636106287/137650000000000 : ℝ)*(4287/50000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (3440049602877566339/3441250000000000000 : ℝ)+2*(300636106287/137650000000000 : ℝ)*(4287/50000 : ℝ)=(312508030318309/312500000000000 : ℝ) by norm_num, show 1+2*(206537759182939/4000000000000000000 : ℝ)=(2000206537759182939/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77676162672658383/100000000000000000000 : ℝ)+(206537759182939/4000000000000000000 : ℝ) ≤ ((3440049602877566339/3441250000000000000 : ℝ)+(300636106287/137650000000000 : ℝ)*((16833/100000 : ℝ)+(4287/50000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (3440049602877566339/3441250000000000000 : ℝ)+(300636106287/137650000000000 : ℝ)*((16833/100000 : ℝ)+(4287/50000 : ℝ))=(1000206078682361/1000000000000000 : ℝ) by norm_num, show 1+(77676162672658383/100000000000000000000 : ℝ)+(206537759182939/4000000000000000000 : ℝ)=(50041419803326115929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77676162672658383/100000000000000000000 : ℝ) ≤ ((3440049602877566339/3441250000000000000 : ℝ)+2*(300636106287/137650000000000 : ℝ)*(16833/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (3440049602877566339/3441250000000000000 : ℝ)+2*(300636106287/137650000000000 : ℝ)*(16833/100000 : ℝ)=(2500966150865333/2500000000000000 : ℝ) by norm_num, show 1+2*(77676162672658383/100000000000000000000 : ℝ)=(50077676162672658383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3440049602877566339/3441250000000000000 : ℝ)*(X 1 0+X 2 0)+(300636106287/137650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (4287/50000 : ℝ)) (hi := (16833/100000 : ℝ)) (c := (3440049602877566339/3441250000000000000 : ℝ)) (alpha := (300636106287/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3440049602877566339/3441250000000000000 : ℝ)*(X 0 1+X 2 1)+(300636106287/137650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (4287/50000 : ℝ)) (hi := (16833/100000 : ℝ)) (c := (3440049602877566339/3441250000000000000 : ℝ)) (alpha := (300636106287/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3440049602877566339/3441250000000000000 : ℝ)*(X 0 2+X 1 2)+(300636106287/137650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (4287/50000 : ℝ)) (hi := (16833/100000 : ℝ)) (c := (3440049602877566339/3441250000000000000 : ℝ)) (alpha := (300636106287/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106248361/5000000000 : ℝ)*X 0 0+(5440849753/10000000000 : ℝ)*X 0 1+(1044254877/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678208141/5000000000 : ℝ)*X 1 0+(-2325017163/10000000000 : ℝ)*X 1 1+(5221274211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334776011/625000000 : ℝ)*X 2 0+(2610637033/5000000000 : ℝ)*X 2 1+(-2325017491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376503267/10000000000 : ℝ)*X 0 0+(3256137/7812500 : ℝ)*X 0 1+(4595803061/10000000000 : ℝ)*X 0 2+(4376503267/10000000000 : ℝ)*X 1 0+(3256137/7812500 : ℝ)*X 1 1+(4595803061/10000000000 : ℝ)*X 1 2+(4376503267/10000000000 : ℝ)*X 2 0+(3256137/7812500 : ℝ)*X 2 1+(4595803061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106260429/5000000000 : ℝ)*X 0 0+(1305548303/2500000000 : ℝ)*X 0 1+(543992541/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301227641/10000000000 : ℝ)*X 1 0+(-2106365203/10000000000 : ℝ)*X 1 1+(2719962963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650613757/5000000000 : ℝ)*X 2 0+(5439925681/10000000000 : ℝ)*X 2 1+(-2106365709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875310061/2000000000 : ℝ)*X 0 0+(4594012597/10000000000 : ℝ)*X 0 1+(2084828343/5000000000 : ℝ)*X 0 2+(875310061/2000000000 : ℝ)*X 1 0+(4594012597/10000000000 : ℝ)*X 1 1+(2084828343/5000000000 : ℝ)*X 1 2+(875310061/2000000000 : ℝ)*X 2 0+(4594012597/10000000000 : ℝ)*X 2 1+(2084828343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255305977619270057689989933/86031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320723007/50000000000000 : ℝ)*(base19) + (76240867/12500000000000 : ℝ)*(base23) + (21291377/50000000000000 : ℝ)*(upper2) + (46984593/25000000000000 : ℝ)*(upper3) + (3445500949705599/100000000000000 : ℝ)*(major0) + (3445500949705599/100000000000000 : ℝ)*(major1) + (3445500949705599/100000000000000 : ℝ)*(major2) + (4554253569880307/100000000000000 : ℝ)*(sp0) + (2277127363985277/50000000000000 : ℝ)*(sp1) + (910850546358697/20000000000000 : ℝ)*(sp2) + (2336739369432111/100000000000000 : ℝ)*(sp3) + (1799536261/100000000000000 : ℝ)*(sp4) + (2027696147/100000000000000 : ℝ)*(sp6) + (7061642653/100000000000000 : ℝ)*(sp7) + (584186607768691/25000000000000 : ℝ)*(f.failure) + (569281921177071/12500000000000 : ℝ)*(f.sum) + (8470059113897/1720625000000000000000000000 : ℝ)*base65 + (1304311074323942939/344125000000000000000000000000000 : ℝ)*base68 + (359082968377307061/344125000000000000000000000000000 : ℝ)*base69 + (364088181408692939/344125000000000000000000000000000 : ℝ)*base72 + (39973531443091/13765000000000000000000000000 : ℝ)*base73 + (2078097926474817939/344125000000000000000000000000000 : ℝ)*base76 + (636443052979942939/344125000000000000000000000000000 : ℝ)*base78 + (170672686616692939/344125000000000000000000000000000 : ℝ)*base80 + (69164913645011/13765000000000000000000000000 : ℝ)*base81 + (2725261/500000000000000000000 : ℝ)*base90 + (2725261/500000000000000000000 : ℝ)*base92 + (2725261/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172703104711453332219984177/34412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1397740213/100000000000000 : ℝ)*(base19) + (1288996603/100000000000000 : ℝ)*(base23) + (2860581/10000000000000 : ℝ)*(upper2) + (9665121/4000000000000 : ℝ)*(upper3) + (694930726261327/20000000000000 : ℝ)*(major0) + (694930726261327/20000000000000 : ℝ)*(major1) + (694930726261327/20000000000000 : ℝ)*(major2) + (28938249591/100000000000000 : ℝ)*(sp1) + (23878346661/100000000000000 : ℝ)*(sp2) + (766845453/50000000000000 : ℝ)*(sp3) + (4592789250549253/100000000000000 : ℝ)*(sp4) + (4592758914559449/100000000000000 : ℝ)*(sp5) + (4592764083205989/100000000000000 : ℝ)*(sp6) + (1178258155542961/50000000000000 : ℝ)*(sp7) + (2356517844776827/100000000000000 : ℝ)*(f.failure) + (4592789250549253/100000000000000 : ℝ)*(f.sum) + (442887860021/688250000000000000000000000 : ℝ)*base65 + (715434230315853147/68825000000000000000000000000000 : ℝ)*base68 + (540355148322703147/68825000000000000000000000000000 : ℝ)*base70 + (458770688111078147/68825000000000000000000000000000 : ℝ)*base72 + (337131786509/172062500000000000000000000 : ℝ)*base74 + (1132370849822328147/68825000000000000000000000000000 : ℝ)*base76 + (124528903808153147/68825000000000000000000000000000 : ℝ)*base78 + (310937764109528147/68825000000000000000000000000000 : ℝ)*base80 + (288897540891/137650000000000000000000000 : ℝ)*base82 + (6290117/2000000000000000000000 : ℝ)*base90 + (6290117/2000000000000000000000 : ℝ)*base92 + (6290117/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1038_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s4_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-6926421/31250000 : ℝ)*x 0 + (5407398473/10000000000 : ℝ)*x 1 + (525214133/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6926421/31250000 : ℝ)^8231 ≤ (13456153394481/100000000000000 : ℝ)^6183 := by
    have hnat : (6926421 : ℕ)^8231*100000000000000^6183 ≤ 13456153394481^6183*31250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6926421 31250000 13456153394481 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407398473/10000000000 : ℝ)^8231 ≤ (44110898205433/100000000000000 : ℝ)^6183 := by
    have hnat : (5407398473 : ℕ)^8231*100000000000000^6183 ≤ 44110898205433^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407398473 10000000000 44110898205433 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525214133/1000000000 : ℝ)^8231 ≤ (10608237095427/25000000000000 : ℝ)^6183 := by
    have hnat : (525214133 : ℕ)^8231*25000000000000^6183 ≤ 10608237095427^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525214133 1000000000 10608237095427 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6926421/31250000 : ℝ), (5407398473/10000000000 : ℝ), (525214133/1000000000 : ℝ)] ![(13456153394481/100000000000000 : ℝ), (44110898205433/100000000000000 : ℝ), (10608237095427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6926421/31250000 : ℝ)|^8231 ≤ (13456153394481/100000000000000 : ℝ)^6183
        have hw : |(-6926421/31250000 : ℝ)|=(6926421/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407398473/10000000000 : ℝ)|^8231 ≤ (44110898205433/100000000000000 : ℝ)^6183
        have hw : |(5407398473/10000000000 : ℝ)|=(5407398473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525214133/1000000000 : ℝ)|^8231 ≤ (10608237095427/25000000000000 : ℝ)^6183
        have hw : |(525214133/1000000000 : ℝ)|=(525214133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2674077903/5000000000 : ℝ)*x 0 + (-2295450369/10000000000 : ℝ)*x 1 + (5252141363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674077903/5000000000 : ℝ)^8231 ≤ (10867180273649/25000000000000 : ℝ)^6183 := by
    have hnat : (2674077903 : ℕ)^8231*25000000000000^6183 ≤ 10867180273649^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674077903 5000000000 10867180273649 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2295450369/10000000000 : ℝ)^8231 ≤ (1762291268501/12500000000000 : ℝ)^6183 := by
    have hnat : (2295450369 : ℕ)^8231*12500000000000^6183 ≤ 1762291268501^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295450369 10000000000 1762291268501 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252141363/10000000000 : ℝ)^8231 ≤ (42432948736631/100000000000000 : ℝ)^6183 := by
    have hnat : (5252141363 : ℕ)^8231*100000000000000^6183 ≤ 42432948736631^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252141363 10000000000 42432948736631 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674077903/5000000000 : ℝ), (-2295450369/10000000000 : ℝ), (5252141363/10000000000 : ℝ)] ![(10867180273649/25000000000000 : ℝ), (1762291268501/12500000000000 : ℝ), (42432948736631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674077903/5000000000 : ℝ)|^8231 ≤ (10867180273649/25000000000000 : ℝ)^6183
        have hw : |(2674077903/5000000000 : ℝ)|=(2674077903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2295450369/10000000000 : ℝ)|^8231 ≤ (1762291268501/12500000000000 : ℝ)^6183
        have hw : |(-2295450369/10000000000 : ℝ)|=(2295450369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252141363/10000000000 : ℝ)|^8231 ≤ (42432948736631/100000000000000 : ℝ)^6183
        have hw : |(5252141363/10000000000 : ℝ)|=(5252141363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534815587/1000000000 : ℝ)*x 0 + (5252141273/10000000000 : ℝ)*x 1 + (-573862601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534815587/1000000000 : ℝ)^8231 ≤ (21734360893537/50000000000000 : ℝ)^6183 := by
    have hnat : (534815587 : ℕ)^8231*50000000000000^6183 ≤ 21734360893537^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534815587 1000000000 21734360893537 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252141273/10000000000 : ℝ)^8231 ≤ (42432947768659/100000000000000 : ℝ)^6183 := by
    have hnat : (5252141273 : ℕ)^8231*100000000000000^6183 ≤ 42432947768659^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252141273 10000000000 42432947768659 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573862601/2500000000 : ℝ)^8231 ≤ (110143206517/781250000000 : ℝ)^6183 := by
    have hnat : (573862601 : ℕ)^8231*781250000000^6183 ≤ 110143206517^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573862601 2500000000 110143206517 781250000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534815587/1000000000 : ℝ), (5252141273/10000000000 : ℝ), (-573862601/2500000000 : ℝ)] ![(21734360893537/50000000000000 : ℝ), (42432947768659/100000000000000 : ℝ), (110143206517/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534815587/1000000000 : ℝ)|^8231 ≤ (21734360893537/50000000000000 : ℝ)^6183
        have hw : |(534815587/1000000000 : ℝ)|=(534815587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252141273/10000000000 : ℝ)|^8231 ≤ (42432947768659/100000000000000 : ℝ)^6183
        have hw : |(5252141273/10000000000 : ℝ)|=(5252141273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-573862601/2500000000 : ℝ)|^8231 ≤ (110143206517/781250000000 : ℝ)^6183
        have hw : |(-573862601/2500000000 : ℝ)|=(573862601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189427439/5000000000 : ℝ)*x 0 + (4230223329/10000000000 : ℝ)*x 1 + (1133203833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189427439/5000000000 : ℝ)^8231 ≤ (16654750364289/50000000000000 : ℝ)^6183 := by
    have hnat : (2189427439 : ℕ)^8231*50000000000000^6183 ≤ 16654750364289^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189427439 5000000000 16654750364289 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230223329/10000000000 : ℝ)^8231 ≤ (15906451958459/50000000000000 : ℝ)^6183 := by
    have hnat : (4230223329 : ℕ)^8231*50000000000000^6183 ≤ 15906451958459^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230223329 10000000000 15906451958459 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133203833/2500000000 : ℝ)^8231 ≤ (34877595341517/100000000000000 : ℝ)^6183 := by
    have hnat : (1133203833 : ℕ)^8231*100000000000000^6183 ≤ 34877595341517^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133203833 2500000000 34877595341517 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189427439/5000000000 : ℝ), (4230223329/10000000000 : ℝ), (1133203833/2500000000 : ℝ)] ![(16654750364289/50000000000000 : ℝ), (15906451958459/50000000000000 : ℝ), (34877595341517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189427439/5000000000 : ℝ)|^8231 ≤ (16654750364289/50000000000000 : ℝ)^6183
        have hw : |(2189427439/5000000000 : ℝ)|=(2189427439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230223329/10000000000 : ℝ)|^8231 ≤ (15906451958459/50000000000000 : ℝ)^6183
        have hw : |(4230223329/10000000000 : ℝ)|=(4230223329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133203833/2500000000 : ℝ)|^8231 ≤ (34877595341517/100000000000000 : ℝ)^6183
        have hw : |(1133203833/2500000000 : ℝ)|=(1133203833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216463469/10000000000 : ℝ)*x 0 + (5252601351/10000000000 : ℝ)*x 1 + (2703468173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216463469/10000000000 : ℝ)^8231 ≤ (13456224103387/100000000000000 : ℝ)^6183 := by
    have hnat : (2216463469 : ℕ)^8231*100000000000000^6183 ≤ 13456224103387^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216463469 10000000000 13456224103387 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252601351/10000000000 : ℝ)^8231 ≤ (21218948045177/50000000000000 : ℝ)^6183 := by
    have hnat : (5252601351 : ℕ)^8231*50000000000000^6183 ≤ 21218948045177^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252601351 10000000000 21218948045177 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703468173/5000000000 : ℝ)^8231 ≤ (8821175959229/20000000000000 : ℝ)^6183 := by
    have hnat : (2703468173 : ℕ)^8231*20000000000000^6183 ≤ 8821175959229^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703468173 5000000000 8821175959229 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216463469/10000000000 : ℝ), (5252601351/10000000000 : ℝ), (2703468173/5000000000 : ℝ)] ![(13456224103387/100000000000000 : ℝ), (21218948045177/50000000000000 : ℝ), (8821175959229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216463469/10000000000 : ℝ)|^8231 ≤ (13456224103387/100000000000000 : ℝ)^6183
        have hw : |(-2216463469/10000000000 : ℝ)|=(2216463469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252601351/10000000000 : ℝ)|^8231 ≤ (21218948045177/50000000000000 : ℝ)^6183
        have hw : |(5252601351/10000000000 : ℝ)|=(5252601351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703468173/5000000000 : ℝ)|^8231 ≤ (8821175959229/20000000000000 : ℝ)^6183
        have hw : |(2703468173/5000000000 : ℝ)|=(2703468173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327284857/2500000000 : ℝ)*x 0 + (-2140655489/10000000000 : ℝ)*x 1 + (84483379/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327284857/2500000000 : ℝ)^8231 ≤ (43047075834399/100000000000000 : ℝ)^6183 := by
    have hnat : (1327284857 : ℕ)^8231*100000000000000^6183 ≤ 43047075834399^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327284857 2500000000 43047075834399 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140655489/10000000000 : ℝ)^8231 ≤ (1605880667047/12500000000000 : ℝ)^6183 := by
    have hnat : (2140655489 : ℕ)^8231*12500000000000^6183 ≤ 1605880667047^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140655489 10000000000 1605880667047 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84483379/156250000 : ℝ)^8231 ≤ (8821175763763/20000000000000 : ℝ)^6183 := by
    have hnat : (84483379 : ℕ)^8231*20000000000000^6183 ≤ 8821175763763^6183*156250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84483379 156250000 8821175763763 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327284857/2500000000 : ℝ), (-2140655489/10000000000 : ℝ), (84483379/156250000 : ℝ)] ![(43047075834399/100000000000000 : ℝ), (1605880667047/12500000000000 : ℝ), (8821175763763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327284857/2500000000 : ℝ)|^8231 ≤ (43047075834399/100000000000000 : ℝ)^6183
        have hw : |(1327284857/2500000000 : ℝ)|=(1327284857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140655489/10000000000 : ℝ)|^8231 ≤ (1605880667047/12500000000000 : ℝ)^6183
        have hw : |(-2140655489/10000000000 : ℝ)|=(2140655489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84483379/156250000 : ℝ)|^8231 ≤ (8821175763763/20000000000000 : ℝ)^6183
        have hw : |(84483379/156250000 : ℝ)|=(84483379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26545697/50000000 : ℝ)*x 0 + (5406936297/10000000000 : ℝ)*x 1 + (-214065547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26545697/50000000 : ℝ)^8231 ≤ (43047075532173/100000000000000 : ℝ)^6183 := by
    have hnat : (26545697 : ℕ)^8231*100000000000000^6183 ≤ 43047075532173^6183*50000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26545697 50000000 43047075532173 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406936297/10000000000 : ℝ)^8231 ≤ (44105879264043/100000000000000 : ℝ)^6183 := by
    have hnat : (5406936297 : ℕ)^8231*100000000000000^6183 ≤ 44105879264043^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406936297 10000000000 44105879264043 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214065547/1000000000 : ℝ)^8231 ≤ (12847045184579/100000000000000 : ℝ)^6183 := by
    have hnat : (214065547 : ℕ)^8231*100000000000000^6183 ≤ 12847045184579^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214065547 1000000000 12847045184579 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26545697/50000000 : ℝ), (5406936297/10000000000 : ℝ), (-214065547/1000000000 : ℝ)] ![(43047075532173/100000000000000 : ℝ), (44105879264043/100000000000000 : ℝ), (12847045184579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26545697/50000000 : ℝ)|^8231 ≤ (43047075532173/100000000000000 : ℝ)^6183
        have hw : |(26545697/50000000 : ℝ)|=(26545697/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406936297/10000000000 : ℝ)|^8231 ≤ (44105879264043/100000000000000 : ℝ)^6183
        have hw : |(5406936297/10000000000 : ℝ)|=(5406936297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214065547/1000000000 : ℝ)|^8231 ≤ (12847045184579/100000000000000 : ℝ)^6183
        have hw : |(-214065547/1000000000 : ℝ)|=(214065547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s4_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378871541/10000000000 : ℝ)*x 0 + (906383607/2000000000 : ℝ)*x 1 + (1652783/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378871541/10000000000 : ℝ)^8231 ≤ (33309669467159/100000000000000 : ℝ)^6183 := by
    have hnat : (4378871541 : ℕ)^8231*100000000000000^6183 ≤ 33309669467159^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378871541 10000000000 33309669467159 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906383607/2000000000 : ℝ)^8231 ≤ (34868404530411/100000000000000 : ℝ)^6183 := by
    have hnat : (906383607 : ℕ)^8231*100000000000000^6183 ≤ 34868404530411^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906383607 2000000000 34868404530411 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1652783/3906250 : ℝ)^8231 ≤ (7955481497097/25000000000000 : ℝ)^6183 := by
    have hnat : (1652783 : ℕ)^8231*25000000000000^6183 ≤ 7955481497097^6183*3906250^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652783 3906250 7955481497097 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378871541/10000000000 : ℝ), (906383607/2000000000 : ℝ), (1652783/3906250 : ℝ)] ![(33309669467159/100000000000000 : ℝ), (34868404530411/100000000000000 : ℝ), (7955481497097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378871541/10000000000 : ℝ)|^8231 ≤ (33309669467159/100000000000000 : ℝ)^6183
        have hw : |(4378871541/10000000000 : ℝ)|=(4378871541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906383607/2000000000 : ℝ)|^8231 ≤ (34868404530411/100000000000000 : ℝ)^6183
        have hw : |(906383607/2000000000 : ℝ)|=(906383607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1652783/3906250 : ℝ)|^8231 ≤ (7955481497097/25000000000000 : ℝ)^6183
        have hw : |(1652783/3906250 : ℝ)|=(1652783/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5151/50000 : ℝ) ^ (4115/1024 : ℝ) ≤ (5399347187342857/50000000000000000000 : ℝ) := by
    have hpowers : (5151/50000 : ℝ)^4115 ≤ (5399347187342857/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5151 : ℕ)^4115*50000000000000000000^1024 ≤ 5399347187342857^1024*50000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5151 50000 5399347187342857 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5151/50000 : ℝ)) (X := (5399347187342857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14947/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (9636742218206867/20000000000000000000 : ℝ) := by
    have hpowers : (14947/100000 : ℝ)^4115 ≤ (9636742218206867/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14947 : ℕ)^4115*20000000000000000000^1024 ≤ 9636742218206867^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14947 100000 9636742218206867 20000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14947/100000 : ℝ)) (X := (9636742218206867/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005399347187342857/25000000000000000000 : ℝ) ≤ (1000053739811401/1000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25005399347187342857/25000000000000000000 : ℝ)^1024 ≤ (1000053739811401/1000000000000000 : ℝ)^4115 := by
      have hnat : (25005399347187342857 : ℕ)^1024*1000000000000000^4115 ≤ 1000053739811401^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005399347187342857 25000000000000000000 1000053739811401 1000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053739811401/1000000000000000 : ℝ)) (X := (25005399347187342857/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058982405465720049/100000000000000000000 : ℝ) ≤ (1250183428335881/1250000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (100058982405465720049/100000000000000000000 : ℝ)^1024 ≤ (1250183428335881/1250000000000000 : ℝ)^4115 := by
      have hnat : (100058982405465720049 : ℕ)^1024*1250000000000000^4115 ≤ 1250183428335881^4115*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058982405465720049 100000000000000000000 1250183428335881 1250000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250183428335881/1250000000000000 : ℝ)) (X := (100058982405465720049/100000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009636742218206867/10000000000000000000 : ℝ) ≤ (5001198727630043/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (10009636742218206867/10000000000000000000 : ℝ)^1024 ≤ (5001198727630043/5000000000000000 : ℝ)^4115 := by
      have hnat : (10009636742218206867 : ℕ)^1024*5000000000000000^4115 ≤ 5001198727630043^4115*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009636742218206867 10000000000000000000 5001198727630043 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001198727630043/5000000000000000 : ℝ)) (X := (10009636742218206867/10000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5399347187342857/50000000000000000000 : ℝ) ≤ ((23216666952760350749/23225000000000000000 : ℝ)+2*(465014286519/232250000000000 : ℝ)*(5151/50000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (23216666952760350749/23225000000000000000 : ℝ)+2*(465014286519/232250000000000 : ℝ)*(5151/50000 : ℝ)=(1000053739811401/1000000000000000 : ℝ) by norm_num, show 1+2*(5399347187342857/50000000000000000000 : ℝ)=(25005399347187342857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9636742218206867/20000000000000000000 : ℝ)+(5399347187342857/50000000000000000000 : ℝ) ≤ ((23216666952760350749/23225000000000000000 : ℝ)+(465014286519/232250000000000 : ℝ)*((14947/100000 : ℝ)+(5151/50000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (23216666952760350749/23225000000000000000 : ℝ)+(465014286519/232250000000000 : ℝ)*((14947/100000 : ℝ)+(5151/50000 : ℝ))=(1250183428335881/1250000000000000 : ℝ) by norm_num, show 1+(9636742218206867/20000000000000000000 : ℝ)+(5399347187342857/50000000000000000000 : ℝ)=(100058982405465720049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9636742218206867/20000000000000000000 : ℝ) ≤ ((23216666952760350749/23225000000000000000 : ℝ)+2*(465014286519/232250000000000 : ℝ)*(14947/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (23216666952760350749/23225000000000000000 : ℝ)+2*(465014286519/232250000000000 : ℝ)*(14947/100000 : ℝ)=(5001198727630043/5000000000000000 : ℝ) by norm_num, show 1+2*(9636742218206867/20000000000000000000 : ℝ)=(10009636742218206867/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23216666952760350749/23225000000000000000 : ℝ)*(X 1 0+X 2 0)+(465014286519/232250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (23216666952760350749/23225000000000000000 : ℝ)) (alpha := (465014286519/232250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23216666952760350749/23225000000000000000 : ℝ)*(X 0 1+X 2 1)+(465014286519/232250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (23216666952760350749/23225000000000000000 : ℝ)) (alpha := (465014286519/232250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23216666952760350749/23225000000000000000 : ℝ)*(X 0 2+X 1 2)+(465014286519/232250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5151/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (23216666952760350749/23225000000000000000 : ℝ)) (alpha := (465014286519/232250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-6926421/31250000 : ℝ)*X 0 0+(5407398473/10000000000 : ℝ)*X 0 1+(525214133/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674077903/5000000000 : ℝ)*X 1 0+(-2295450369/10000000000 : ℝ)*X 1 1+(5252141363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534815587/1000000000 : ℝ)*X 2 0+(5252141273/10000000000 : ℝ)*X 2 1+(-573862601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189427439/5000000000 : ℝ)*X 0 0+(4230223329/10000000000 : ℝ)*X 0 1+(1133203833/2500000000 : ℝ)*X 0 2+(2189427439/5000000000 : ℝ)*X 1 0+(4230223329/10000000000 : ℝ)*X 1 1+(1133203833/2500000000 : ℝ)*X 1 2+(2189427439/5000000000 : ℝ)*X 2 0+(4230223329/10000000000 : ℝ)*X 2 1+(1133203833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216463469/10000000000 : ℝ)*X 0 0+(5252601351/10000000000 : ℝ)*X 0 1+(2703468173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327284857/2500000000 : ℝ)*X 1 0+(-2140655489/10000000000 : ℝ)*X 1 1+(84483379/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26545697/50000000 : ℝ)*X 2 0+(5406936297/10000000000 : ℝ)*X 2 1+(-214065547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378871541/10000000000 : ℝ)*X 0 0+(906383607/2000000000 : ℝ)*X 0 1+(1652783/3906250 : ℝ)*X 0 2+(4378871541/10000000000 : ℝ)*X 1 0+(906383607/2000000000 : ℝ)*X 1 1+(1652783/3906250 : ℝ)*X 1 2+(4378871541/10000000000 : ℝ)*X 2 0+(906383607/2000000000 : ℝ)*X 2 1+(1652783/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (675848863508960191616495157/116125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124747713/10000000000000 : ℝ)*(base19) + (1283953773/100000000000000 : ℝ)*(base23) + (10857013/50000000000000 : ℝ)*(lower2) + (167845807/100000000000000 : ℝ)*(upper3) + (53010587/50000000000000 : ℝ)*(upper5) + (487289857091531/10000000000000 : ℝ)*(major0) + (487289857091531/10000000000000 : ℝ)*(major1) + (487289857091531/10000000000000 : ℝ)*(major2) + (201279921030349/3125000000000 : ℝ)*(sp0) + (3220492509010031/50000000000000 : ℝ)*(sp1) + (6440984981543419/100000000000000 : ℝ)*(sp2) + (330479450619987/10000000000000 : ℝ)*(sp3) + (3599065753/12500000000000 : ℝ)*(sp4) + (8088066581/50000000000000 : ℝ)*(sp7) + (413101335291629/12500000000000 : ℝ)*(f.failure) + (805123283187149/12500000000000 : ℝ)*(f.sum) + (9462799078057/2322500000000000000000000000 : ℝ)*base66 + (1267948613396693281/232250000000000000000000000000000 : ℝ)*base68 + (897428326222306719/232250000000000000000000000000000 : ℝ)*base69 + (537409674529806719/232250000000000000000000000000000 : ℝ)*base71 + (3279288532417/2322500000000000000000000000 : ℝ)*base74 + (2894374070252193281/232250000000000000000000000000000 : ℝ)*base76 + (1500570037815693281/232250000000000000000000000000000 : ℝ)*base78 + (1079860370039443281/232250000000000000000000000000000 : ℝ)*base80 + (2715905241547/580625000000000000000000000 : ℝ)*base81 + (178541/250000000000000000000 : ℝ)*base89 + (178541/250000000000000000000 : ℝ)*base91 + (178541/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1682923758145125736646511/625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370177323/50000000000000 : ℝ)*(base19) + (233501351/25000000000000 : ℝ)*(base23) + (16337071/12500000000000 : ℝ)*(upper2) + (66736369/25000000000000 : ℝ)*(upper5) + (4901979620561823/100000000000000 : ℝ)*(major0) + (4901979620561823/100000000000000 : ℝ)*(major1) + (4901979620561823/100000000000000 : ℝ)*(major2) + (1607524801/50000000000000 : ℝ)*(sp0) + (4283114723/20000000000000 : ℝ)*(sp1) + (9459277061/50000000000000 : ℝ)*(sp2) + (809927802654297/12500000000000 : ℝ)*(sp4) + (6479403480355717/100000000000000 : ℝ)*(sp5) + (3239702891862227/50000000000000 : ℝ)*(sp6) + (132981340603349/4000000000000 : ℝ)*(sp7) + (132981340603349/4000000000000 : ℝ)*(f.failure) + (6479425636283979/100000000000000 : ℝ)*(f.sum) + (63366700363951/23225000000000000000000000000 : ℝ)*base66 + (5017689635050055427/2322500000000000000000000000000000 : ℝ)*base67 + (12099018474522555427/2322500000000000000000000000000000 : ℝ)*base69 + (38705183568235055427/2322500000000000000000000000000000 : ℝ)*base71 + (150199108403801/23225000000000000000000000000 : ℝ)*base74 + (4449093559300055427/2322500000000000000000000000000000 : ℝ)*base75 + (18988749076620055427/2322500000000000000000000000000000 : ℝ)*base77 + (15606770935044944573/2322500000000000000000000000000000 : ℝ)*base80 + (11613709028713/11612500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (102421/80000000000000000000 : ℝ)*base89 + (102421/80000000000000000000 : ℝ)*base91 + (102421/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s5_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217369419/10000000000 : ℝ)*x 0 + (2698906511/5000000000 : ℝ)*x 1 + (2630563473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217369419/10000000000 : ℝ)^8231 ≤ (13463546438707/100000000000000 : ℝ)^6183 := by
    have hnat : (2217369419 : ℕ)^8231*100000000000000^6183 ≤ 13463546438707^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217369419 10000000000 13463546438707 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698906511/5000000000 : ℝ)^8231 ≤ (44006835319729/100000000000000 : ℝ)^6183 := by
    have hnat : (2698906511 : ℕ)^8231*100000000000000^6183 ≤ 44006835319729^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698906511 5000000000 44006835319729 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630563473/5000000000 : ℝ)^8231 ≤ (664525284733/1562500000000 : ℝ)^6183 := by
    have hnat : (2630563473 : ℕ)^8231*1562500000000^6183 ≤ 664525284733^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630563473 5000000000 664525284733 1562500000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217369419/10000000000 : ℝ), (2698906511/5000000000 : ℝ), (2630563473/5000000000 : ℝ)] ![(13463546438707/100000000000000 : ℝ), (44006835319729/100000000000000 : ℝ), (664525284733/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217369419/10000000000 : ℝ)|^8231 ≤ (13463546438707/100000000000000 : ℝ)^6183
        have hw : |(-2217369419/10000000000 : ℝ)|=(2217369419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698906511/5000000000 : ℝ)|^8231 ≤ (44006835319729/100000000000000 : ℝ)^6183
        have hw : |(2698906511/5000000000 : ℝ)|=(2698906511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630563473/5000000000 : ℝ)|^8231 ≤ (664525284733/1562500000000 : ℝ)^6183
        have hw : |(2630563473/5000000000 : ℝ)|=(2630563473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336443709/2500000000 : ℝ)*x 0 + (-2286772321/10000000000 : ℝ)*x 1 + (5261126937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336443709/2500000000 : ℝ)^8231 ≤ (1086074024093/2500000000000 : ℝ)^6183 := by
    have hnat : (1336443709 : ℕ)^8231*2500000000000^6183 ≤ 1086074024093^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336443709 2500000000 1086074024093 2500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286772321/10000000000 : ℝ)^8231 ≤ (2805484178067/20000000000000 : ℝ)^6183 := by
    have hnat : (2286772321 : ℕ)^8231*20000000000000^6183 ≤ 2805484178067^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286772321 10000000000 2805484178067 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261126937/10000000000 : ℝ)^8231 ≤ (2126480906303/5000000000000 : ℝ)^6183 := by
    have hnat : (5261126937 : ℕ)^8231*5000000000000^6183 ≤ 2126480906303^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261126937 10000000000 2126480906303 5000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336443709/2500000000 : ℝ), (-2286772321/10000000000 : ℝ), (5261126937/10000000000 : ℝ)] ![(1086074024093/2500000000000 : ℝ), (2805484178067/20000000000000 : ℝ), (2126480906303/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336443709/2500000000 : ℝ)|^8231 ≤ (1086074024093/2500000000000 : ℝ)^6183
        have hw : |(1336443709/2500000000 : ℝ)|=(1336443709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286772321/10000000000 : ℝ)|^8231 ≤ (2805484178067/20000000000000 : ℝ)^6183
        have hw : |(-2286772321/10000000000 : ℝ)|=(2286772321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261126937/10000000000 : ℝ)|^8231 ≤ (2126480906303/5000000000000 : ℝ)^6183
        have hw : |(5261126937/10000000000 : ℝ)|=(5261126937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069154971/2000000000 : ℝ)*x 0 + (2630563463/5000000000 : ℝ)*x 1 + (-228677231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069154971/2000000000 : ℝ)^8231 ≤ (43442961169269/100000000000000 : ℝ)^6183 := by
    have hnat : (1069154971 : ℕ)^8231*100000000000000^6183 ≤ 43442961169269^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069154971 2000000000 43442961169269 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630563463/5000000000 : ℝ)^8231 ≤ (21264809003843/50000000000000 : ℝ)^6183 := by
    have hnat : (2630563463 : ℕ)^8231*50000000000000^6183 ≤ 21264809003843^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630563463 5000000000 21264809003843 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228677231/1000000000 : ℝ)^8231 ≤ (14027420800509/100000000000000 : ℝ)^6183 := by
    have hnat : (228677231 : ℕ)^8231*100000000000000^6183 ≤ 14027420800509^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228677231 1000000000 14027420800509 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069154971/2000000000 : ℝ), (2630563463/5000000000 : ℝ), (-228677231/1000000000 : ℝ)] ![(43442961169269/100000000000000 : ℝ), (21264809003843/50000000000000 : ℝ), (14027420800509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069154971/2000000000 : ℝ)|^8231 ≤ (43442961169269/100000000000000 : ℝ)^6183
        have hw : |(1069154971/2000000000 : ℝ)|=(1069154971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630563463/5000000000 : ℝ)|^8231 ≤ (21264809003843/50000000000000 : ℝ)^6183
        have hw : |(2630563463/5000000000 : ℝ)|=(2630563463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228677231/1000000000 : ℝ)|^8231 ≤ (14027420800509/100000000000000 : ℝ)^6183
        have hw : |(-228677231/1000000000 : ℝ)|=(228677231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379383857/10000000000 : ℝ)*x 0 + (849650161/2000000000 : ℝ)*x 1 + (2257324127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379383857/10000000000 : ℝ)^8231 ≤ (33314857560819/100000000000000 : ℝ)^6183 := by
    have hnat : (4379383857 : ℕ)^8231*100000000000000^6183 ≤ 33314857560819^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379383857 10000000000 33314857560819 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849650161/2000000000 : ℝ)^8231 ≤ (7998377712613/25000000000000 : ℝ)^6183 := by
    have hnat : (849650161 : ℕ)^8231*25000000000000^6183 ≤ 7998377712613^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849650161 2000000000 7998377712613 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257324127/5000000000 : ℝ)^8231 ≤ (17345815790711/50000000000000 : ℝ)^6183 := by
    have hnat : (2257324127 : ℕ)^8231*50000000000000^6183 ≤ 17345815790711^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257324127 5000000000 17345815790711 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379383857/10000000000 : ℝ), (849650161/2000000000 : ℝ), (2257324127/5000000000 : ℝ)] ![(33314857560819/100000000000000 : ℝ), (7998377712613/25000000000000 : ℝ), (17345815790711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379383857/10000000000 : ℝ)|^8231 ≤ (33314857560819/100000000000000 : ℝ)^6183
        have hw : |(4379383857/10000000000 : ℝ)|=(4379383857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849650161/2000000000 : ℝ)|^8231 ≤ (7998377712613/25000000000000 : ℝ)^6183
        have hw : |(849650161/2000000000 : ℝ)|=(849650161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257324127/5000000000 : ℝ)|^8231 ≤ (17345815790711/50000000000000 : ℝ)^6183
        have hw : |(2257324127/5000000000 : ℝ)|=(2257324127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108687631/5000000000 : ℝ)*x 0 + (82210687/156250000 : ℝ)*x 1 + (5397454661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108687631/5000000000 : ℝ)^8231 ≤ (420737302123/3125000000000 : ℝ)^6183 := by
    have hnat : (1108687631 : ℕ)^8231*3125000000000^6183 ≤ 420737302123^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108687631 5000000000 420737302123 3125000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82210687/156250000 : ℝ)^8231 ≤ (21266730149307/50000000000000 : ℝ)^6183 := by
    have hnat : (82210687 : ℕ)^8231*50000000000000^6183 ≤ 21266730149307^6183*156250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82210687 156250000 21266730149307 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397454661/10000000000 : ℝ)^8231 ≤ (44002946018139/100000000000000 : ℝ)^6183 := by
    have hnat : (5397454661 : ℕ)^8231*100000000000000^6183 ≤ 44002946018139^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397454661 10000000000 44002946018139 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108687631/5000000000 : ℝ), (82210687/156250000 : ℝ), (5397454661/10000000000 : ℝ)] ![(420737302123/3125000000000 : ℝ), (21266730149307/50000000000000 : ℝ), (44002946018139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108687631/5000000000 : ℝ)|^8231 ≤ (420737302123/3125000000000 : ℝ)^6183
        have hw : |(-1108687631/5000000000 : ℝ)|=(1108687631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82210687/156250000 : ℝ)|^8231 ≤ (21266730149307/50000000000000 : ℝ)^6183
        have hw : |(82210687/156250000 : ℝ)|=(82210687/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397454661/10000000000 : ℝ)|^8231 ≤ (44002946018139/100000000000000 : ℝ)^6183
        have hw : |(5397454661/10000000000 : ℝ)|=(5397454661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311424403/10000000000 : ℝ)*x 0 + (-1075222303/5000000000 : ℝ)*x 1 + (5397454661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311424403/10000000000 : ℝ)^8231 ≤ (43071741070913/100000000000000 : ℝ)^6183 := by
    have hnat : (5311424403 : ℕ)^8231*100000000000000^6183 ≤ 43071741070913^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311424403 10000000000 43071741070913 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075222303/5000000000 : ℝ)^8231 ≤ (12925312898567/100000000000000 : ℝ)^6183 := by
    have hnat : (1075222303 : ℕ)^8231*100000000000000^6183 ≤ 12925312898567^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075222303 5000000000 12925312898567 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397454661/10000000000 : ℝ)^8231 ≤ (44002946018139/100000000000000 : ℝ)^6183 := by
    have hnat : (5397454661 : ℕ)^8231*100000000000000^6183 ≤ 44002946018139^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397454661 10000000000 44002946018139 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311424403/10000000000 : ℝ), (-1075222303/5000000000 : ℝ), (5397454661/10000000000 : ℝ)] ![(43071741070913/100000000000000 : ℝ), (12925312898567/100000000000000 : ℝ), (44002946018139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311424403/10000000000 : ℝ)|^8231 ≤ (43071741070913/100000000000000 : ℝ)^6183
        have hw : |(5311424403/10000000000 : ℝ)|=(5311424403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075222303/5000000000 : ℝ)|^8231 ≤ (12925312898567/100000000000000 : ℝ)^6183
        have hw : |(-1075222303/5000000000 : ℝ)|=(1075222303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397454661/10000000000 : ℝ)|^8231 ≤ (44002946018139/100000000000000 : ℝ)^6183
        have hw : |(5397454661/10000000000 : ℝ)|=(5397454661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327856101/2500000000 : ℝ)*x 0 + (5397454659/10000000000 : ℝ)*x 1 + (-33600697/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327856101/2500000000 : ℝ)^8231 ≤ (10767935270427/25000000000000 : ℝ)^6183 := by
    have hnat : (1327856101 : ℕ)^8231*25000000000000^6183 ≤ 10767935270427^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327856101 2500000000 10767935270427 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397454659/10000000000 : ℝ)^8231 ≤ (44002945996433/100000000000000 : ℝ)^6183 := by
    have hnat : (5397454659 : ℕ)^8231*100000000000000^6183 ≤ 44002945996433^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397454659 10000000000 44002945996433 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33600697/156250000 : ℝ)^8231 ≤ (1292531291457/10000000000000 : ℝ)^6183 := by
    have hnat : (33600697 : ℕ)^8231*10000000000000^6183 ≤ 1292531291457^6183*156250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33600697 156250000 1292531291457 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327856101/2500000000 : ℝ), (5397454659/10000000000 : ℝ), (-33600697/156250000 : ℝ)] ![(10767935270427/25000000000000 : ℝ), (44002945996433/100000000000000 : ℝ), (1292531291457/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327856101/2500000000 : ℝ)|^8231 ≤ (10767935270427/25000000000000 : ℝ)^6183
        have hw : |(1327856101/2500000000 : ℝ)|=(1327856101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397454659/10000000000 : ℝ)|^8231 ≤ (44002945996433/100000000000000 : ℝ)^6183
        have hw : |(5397454659/10000000000 : ℝ)|=(5397454659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33600697/156250000 : ℝ)|^8231 ≤ (1292531291457/10000000000000 : ℝ)^6183
        have hw : |(-33600697/156250000 : ℝ)|=(33600697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s5_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379395263/10000000000 : ℝ)*x 0 + (564244053/1250000000 : ℝ)*x 1 + (1062237309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379395263/10000000000 : ℝ)^8231 ≤ (8328743267191/25000000000000 : ℝ)^6183 := by
    have hnat : (4379395263 : ℕ)^8231*25000000000000^6183 ≤ 8328743267191^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379395263 10000000000 8328743267191 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564244053/1250000000 : ℝ)^8231 ≤ (34684513774151/100000000000000 : ℝ)^6183 := by
    have hnat : (564244053 : ℕ)^8231*100000000000000^6183 ≤ 34684513774151^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564244053 1250000000 34684513774151 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062237309/2500000000 : ℝ)^8231 ≤ (3200051314603/10000000000000 : ℝ)^6183 := by
    have hnat : (1062237309 : ℕ)^8231*10000000000000^6183 ≤ 3200051314603^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062237309 2500000000 3200051314603 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379395263/10000000000 : ℝ), (564244053/1250000000 : ℝ), (1062237309/2500000000 : ℝ)] ![(8328743267191/25000000000000 : ℝ), (34684513774151/100000000000000 : ℝ), (3200051314603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379395263/10000000000 : ℝ)|^8231 ≤ (8328743267191/25000000000000 : ℝ)^6183
        have hw : |(4379395263/10000000000 : ℝ)|=(4379395263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564244053/1250000000 : ℝ)|^8231 ≤ (34684513774151/100000000000000 : ℝ)^6183
        have hw : |(564244053/1250000000 : ℝ)|=(564244053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062237309/2500000000 : ℝ)|^8231 ≤ (3200051314603/10000000000000 : ℝ)^6183
        have hw : |(1062237309/2500000000 : ℝ)|=(1062237309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11153/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10961/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (13854326908589553/100000000000000000000 : ℝ) := by
    have hpowers : (10961/100000 : ℝ)^4115 ≤ (13854326908589553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10961 : ℕ)^4115*100000000000000000000^1024 ≤ 13854326908589553^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10961 100000 13854326908589553 100000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10961/100000 : ℝ)) (X := (13854326908589553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (4115/1024 : ℝ) ≤ (39747863892388309/100000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^4115 ≤ (39747863892388309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1781 : ℕ)^4115*100000000000000000000^1024 ≤ 39747863892388309^1024*12500^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 39747863892388309 100000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (39747863892388309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013854326908589553/50000000000000000000 : ℝ) ≤ (2000137889230687/2000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50013854326908589553/50000000000000000000 : ℝ)^1024 ≤ (2000137889230687/2000000000000000 : ℝ)^4115 := by
      have hnat : (50013854326908589553 : ℕ)^1024*2000000000000000^4115 ≤ 2000137889230687^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013854326908589553 50000000000000000000 2000137889230687 2000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000137889230687/2000000000000000 : ℝ)) (X := (50013854326908589553/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026801095400488931/50000000000000000000 : ℝ) ≤ (10001333598949873/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50026801095400488931/50000000000000000000 : ℝ)^1024 ≤ (10001333598949873/10000000000000000 : ℝ)^4115 := by
      have hnat : (50026801095400488931 : ℕ)^1024*10000000000000000^4115 ≤ 10001333598949873^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026801095400488931 50000000000000000000 10001333598949873 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001333598949873/10000000000000000 : ℝ)) (X := (50026801095400488931/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039747863892388309/50000000000000000000 : ℝ) ≤ (10001977751746311/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50039747863892388309/50000000000000000000 : ℝ)^1024 ≤ (10001977751746311/10000000000000000 : ℝ)^4115 := by
      have hnat : (50039747863892388309 : ℕ)^1024*10000000000000000^4115 ≤ 10001977751746311^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039747863892388309 50000000000000000000 10001977751746311 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001977751746311/10000000000000000 : ℝ)) (X := (50039747863892388309/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13854326908589553/100000000000000000000 : ℝ) ≤ ((32858145091902827009/32870000000000000000 : ℝ)+2*(322076398219/164350000000000 : ℝ)*(10961/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (32858145091902827009/32870000000000000000 : ℝ)+2*(322076398219/164350000000000 : ℝ)*(10961/100000 : ℝ)=(2000137889230687/2000000000000000 : ℝ) by norm_num, show 1+2*(13854326908589553/100000000000000000000 : ℝ)=(50013854326908589553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39747863892388309/100000000000000000000 : ℝ)+(13854326908589553/100000000000000000000 : ℝ) ≤ ((32858145091902827009/32870000000000000000 : ℝ)+(322076398219/164350000000000 : ℝ)*((1781/12500 : ℝ)+(10961/100000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (32858145091902827009/32870000000000000000 : ℝ)+(322076398219/164350000000000 : ℝ)*((1781/12500 : ℝ)+(10961/100000 : ℝ))=(10001333598949873/10000000000000000 : ℝ) by norm_num, show 1+(39747863892388309/100000000000000000000 : ℝ)+(13854326908589553/100000000000000000000 : ℝ)=(50026801095400488931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39747863892388309/100000000000000000000 : ℝ) ≤ ((32858145091902827009/32870000000000000000 : ℝ)+2*(322076398219/164350000000000 : ℝ)*(1781/12500 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (32858145091902827009/32870000000000000000 : ℝ)+2*(322076398219/164350000000000 : ℝ)*(1781/12500 : ℝ)=(10001977751746311/10000000000000000 : ℝ) by norm_num, show 1+2*(39747863892388309/100000000000000000000 : ℝ)=(50039747863892388309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32858145091902827009/32870000000000000000 : ℝ)*(X 1 0+X 2 0)+(322076398219/164350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (32858145091902827009/32870000000000000000 : ℝ)) (alpha := (322076398219/164350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32858145091902827009/32870000000000000000 : ℝ)*(X 0 1+X 2 1)+(322076398219/164350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (32858145091902827009/32870000000000000000 : ℝ)) (alpha := (322076398219/164350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32858145091902827009/32870000000000000000 : ℝ)*(X 0 2+X 1 2)+(322076398219/164350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (32858145091902827009/32870000000000000000 : ℝ)) (alpha := (322076398219/164350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2217369419/10000000000 : ℝ)*X 0 0+(2698906511/5000000000 : ℝ)*X 0 1+(2630563473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336443709/2500000000 : ℝ)*X 1 0+(-2286772321/10000000000 : ℝ)*X 1 1+(5261126937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069154971/2000000000 : ℝ)*X 2 0+(2630563463/5000000000 : ℝ)*X 2 1+(-228677231/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379383857/10000000000 : ℝ)*X 0 0+(849650161/2000000000 : ℝ)*X 0 1+(2257324127/5000000000 : ℝ)*X 0 2+(4379383857/10000000000 : ℝ)*X 1 0+(849650161/2000000000 : ℝ)*X 1 1+(2257324127/5000000000 : ℝ)*X 1 2+(4379383857/10000000000 : ℝ)*X 2 0+(849650161/2000000000 : ℝ)*X 2 1+(2257324127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1108687631/5000000000 : ℝ)*X 0 0+(82210687/156250000 : ℝ)*X 0 1+(5397454661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311424403/10000000000 : ℝ)*X 1 0+(-1075222303/5000000000 : ℝ)*X 1 1+(5397454661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327856101/2500000000 : ℝ)*X 2 0+(5397454659/10000000000 : ℝ)*X 2 1+(-33600697/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379395263/10000000000 : ℝ)*X 0 0+(564244053/1250000000 : ℝ)*X 0 1+(1062237309/2500000000 : ℝ)*X 0 2+(4379395263/10000000000 : ℝ)*X 1 0+(564244053/1250000000 : ℝ)*X 1 1+(1062237309/2500000000 : ℝ)*X 1 2+(4379395263/10000000000 : ℝ)*X 2 0+(564244053/1250000000 : ℝ)*X 2 1+(1062237309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3894769089503145652356733779/1643500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51896543/10000000000000 : ℝ)*(base19) + (262628083/50000000000000 : ℝ)*(base23) + (10537631/100000000000000 : ℝ)*(lower2) + (8648021/20000000000000 : ℝ)*(upper3) + (24870519/50000000000000 : ℝ)*(upper5) + (5534932990603823/100000000000000 : ℝ)*(major0) + (5534932990603823/100000000000000 : ℝ)*(major1) + (5534932990603823/100000000000000 : ℝ)*(major2) + (7316047614498333/100000000000000 : ℝ)*(sp0) + (3658030740235221/50000000000000 : ℝ)*(sp1) + (3658030737089853/50000000000000 : ℝ)*(sp2) + (1876898363136781/50000000000000 : ℝ)*(sp3) + (7192468769/50000000000000 : ℝ)*(sp4) + (897063101/12500000000000 : ℝ)*(sp7) + (375380390277837/10000000000000 : ℝ)*(f.failure) + (7316061999435873/100000000000000 : ℝ)*(f.sum) + (17541114997451/16435000000000000000000000000 : ℝ)*base66 + (32307309672726455407/3287000000000000000000000000000000 : ℝ)*base67 + (10431082318206455407/3287000000000000000000000000000000 : ℝ)*base69 + (59517570519320455407/3287000000000000000000000000000000 : ℝ)*base71 + (9330879774863/8217500000000000000000000000 : ℝ)*base74 + (85378888434459544593/3287000000000000000000000000000000 : ℝ)*base76 + (60172685666454455407/3287000000000000000000000000000000 : ℝ)*base77 + (1437954810675544593/3287000000000000000000000000000000 : ℝ)*base80 + (30327499947043/8217500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1836173/200000000000000000000 : ℝ)*base89 + (1836173/200000000000000000000 : ℝ)*base91 + (1836173/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3496923237127735403114232363/328700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15968131/800000000000 : ℝ)*(base19) + (33888863/1562500000000 : ℝ)*(base23) + (212399423/100000000000000 : ℝ)*(upper3) + (392339/500000000000 : ℝ)*(lower4) + (218300383/100000000000000 : ℝ)*(upper5) + (1112806349478477/20000000000000 : ℝ)*(major0) + (1112806349478477/20000000000000 : ℝ)*(major1) + (1112806349478477/20000000000000 : ℝ)*(major2) + (6475903651/12500000000000 : ℝ)*(sp1) + (55479874929/100000000000000 : ℝ)*(sp2) + (7354524395610893/100000000000000 : ℝ)*(sp4) + (735447059236531/10000000000000 : ℝ)*(sp5) + (1838616686712183/25000000000000 : ℝ)*(sp6) + (754707748910461/20000000000000 : ℝ)*(sp7) + (754707748910461/20000000000000 : ℝ)*(f.failure) + (7354524395610893/100000000000000 : ℝ)*(f.sum) + (1363734272463/3287000000000000000000000000 : ℝ)*base65 + (8344254586486785293/657400000000000000000000000000000 : ℝ)*base67 + (2694683557870185293/657400000000000000000000000000000 : ℝ)*base69 + (9354546716498185293/657400000000000000000000000000000 : ℝ)*base71 + (2053846169339/1643500000000000000000000000 : ℝ)*base74 + (10155540131275985293/657400000000000000000000000000000 : ℝ)*base75 + (7251460871331185293/657400000000000000000000000000000 : ℝ)*base77 + (15516345787373585293/657400000000000000000000000000000 : ℝ)*base79 + (1971087737533/821750000000000000000000000 : ℝ)*base82 + (155069/400000000000000000000 : ℝ)*base89 + (155069/400000000000000000000 : ℝ)*base91 + (155069/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1038_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1038_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1038_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1038_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
