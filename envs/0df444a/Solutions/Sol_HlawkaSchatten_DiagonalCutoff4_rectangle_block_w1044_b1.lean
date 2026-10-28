-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:56.859669+00:00
-- url     : https://prove2.me/submissions/8efac1ba-6339-48e7-82fd-30f2e09a1964

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
theorem support_rectangle_w1044_s3_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-276200017/1250000000 : ℝ)*x 0 + (2720077081/5000000000 : ℝ)*x 1 + (652740601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276200017/1250000000 : ℝ)^8237 ≤ (13407281911579/100000000000000 : ℝ)^6189 := by
    have hnat : (276200017 : ℕ)^8237*100000000000000^6189 ≤ 13407281911579^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276200017 1250000000 13407281911579 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720077081/5000000000 : ℝ)^8237 ≤ (44475659460623/100000000000000 : ℝ)^6189 := by
    have hnat : (2720077081 : ℕ)^8237*100000000000000^6189 ≤ 44475659460623^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720077081 5000000000 44475659460623 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652740601/1250000000 : ℝ)^8237 ≤ (10529264654627/25000000000000 : ℝ)^6189 := by
    have hnat : (652740601 : ℕ)^8237*25000000000000^6189 ≤ 10529264654627^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652740601 1250000000 10529264654627 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276200017/1250000000 : ℝ), (2720077081/5000000000 : ℝ), (652740601/1250000000 : ℝ)] ![(13407281911579/100000000000000 : ℝ), (44475659460623/100000000000000 : ℝ), (10529264654627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276200017/1250000000 : ℝ)|^8237 ≤ (13407281911579/100000000000000 : ℝ)^6189
        have hw : |(-276200017/1250000000 : ℝ)|=(276200017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720077081/5000000000 : ℝ)|^8237 ≤ (44475659460623/100000000000000 : ℝ)^6189
        have hw : |(2720077081/5000000000 : ℝ)|=(2720077081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652740601/1250000000 : ℝ)|^8237 ≤ (10529264654627/25000000000000 : ℝ)^6189
        have hw : |(652740601/1250000000 : ℝ)|=(652740601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356264959/10000000000 : ℝ)*x 0 + (-2321413849/10000000000 : ℝ)*x 1 + (2610962467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356264959/10000000000 : ℝ)^8237 ≤ (43565216941817/100000000000000 : ℝ)^6189 := by
    have hnat : (5356264959 : ℕ)^8237*100000000000000^6189 ≤ 43565216941817^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356264959 10000000000 43565216941817 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2321413849/10000000000 : ℝ)^8237 ≤ (1789715384059/12500000000000 : ℝ)^6189 := by
    have hnat : (2321413849 : ℕ)^8237*12500000000000^6189 ≤ 1789715384059^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2321413849 10000000000 1789715384059 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610962467/5000000000 : ℝ)^8237 ≤ (42117059971037/100000000000000 : ℝ)^6189 := by
    have hnat : (2610962467 : ℕ)^8237*100000000000000^6189 ≤ 42117059971037^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610962467 5000000000 42117059971037 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356264959/10000000000 : ℝ), (-2321413849/10000000000 : ℝ), (2610962467/5000000000 : ℝ)] ![(43565216941817/100000000000000 : ℝ), (1789715384059/12500000000000 : ℝ), (42117059971037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356264959/10000000000 : ℝ)|^8237 ≤ (43565216941817/100000000000000 : ℝ)^6189
        have hw : |(5356264959/10000000000 : ℝ)|=(5356264959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2321413849/10000000000 : ℝ)|^8237 ≤ (1789715384059/12500000000000 : ℝ)^6189
        have hw : |(-2321413849/10000000000 : ℝ)|=(2321413849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610962467/5000000000 : ℝ)|^8237 ≤ (42117059971037/100000000000000 : ℝ)^6189
        have hw : |(2610962467/5000000000 : ℝ)|=(2610962467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267813249/500000000 : ℝ)*x 0 + (5221925061/10000000000 : ℝ)*x 1 + (-464282731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267813249/500000000 : ℝ)^8237 ≤ (43565217169141/100000000000000 : ℝ)^6189 := by
    have hnat : (267813249 : ℕ)^8237*100000000000000^6189 ≤ 43565217169141^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267813249 500000000 43565217169141 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221925061/10000000000 : ℝ)^8237 ≤ (421170613343/1000000000000 : ℝ)^6189 := by
    have hnat : (5221925061 : ℕ)^8237*1000000000000^6189 ≤ 421170613343^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221925061 10000000000 421170613343 1000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464282731/2000000000 : ℝ)^8237 ≤ (357943037/2500000000 : ℝ)^6189 := by
    have hnat : (464282731 : ℕ)^8237*2500000000^6189 ≤ 357943037^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464282731 2000000000 357943037 2500000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267813249/500000000 : ℝ), (5221925061/10000000000 : ℝ), (-464282731/2000000000 : ℝ)] ![(43565217169141/100000000000000 : ℝ), (421170613343/1000000000000 : ℝ), (357943037/2500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267813249/500000000 : ℝ)|^8237 ≤ (43565217169141/100000000000000 : ℝ)^6189
        have hw : |(267813249/500000000 : ℝ)|=(267813249/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221925061/10000000000 : ℝ)|^8237 ≤ (421170613343/1000000000000 : ℝ)^6189
        have hw : |(5221925061/10000000000 : ℝ)|=(5221925061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464282731/2000000000 : ℝ)|^8237 ≤ (357943037/2500000000 : ℝ)^6189
        have hw : |(-464282731/2000000000 : ℝ)|=(464282731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375682781/10000000000 : ℝ)*x 0 + (521004231/1250000000 : ℝ)*x 1 + (4593865049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375682781/10000000000 : ℝ)^8237 ≤ (8321553881733/25000000000000 : ℝ)^6189 := by
    have hnat : (4375682781 : ℕ)^8237*25000000000000^6189 ≤ 8321553881733^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375682781 10000000000 8321553881733 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521004231/1250000000 : ℝ)^8237 ≤ (6240117978147/20000000000000 : ℝ)^6189 := by
    have hnat : (521004231 : ℕ)^8237*20000000000000^6189 ≤ 6240117978147^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521004231 1250000000 6240117978147 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4593865049/10000000000 : ℝ)^8237 ≤ (8878298642521/25000000000000 : ℝ)^6189 := by
    have hnat : (4593865049 : ℕ)^8237*25000000000000^6189 ≤ 8878298642521^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593865049 10000000000 8878298642521 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375682781/10000000000 : ℝ), (521004231/1250000000 : ℝ), (4593865049/10000000000 : ℝ)] ![(8321553881733/25000000000000 : ℝ), (6240117978147/20000000000000 : ℝ), (8878298642521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375682781/10000000000 : ℝ)|^8237 ≤ (8321553881733/25000000000000 : ℝ)^6189
        have hw : |(4375682781/10000000000 : ℝ)|=(4375682781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521004231/1250000000 : ℝ)|^8237 ≤ (6240117978147/20000000000000 : ℝ)^6189
        have hw : |(521004231/1250000000 : ℝ)|=(521004231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4593865049/10000000000 : ℝ)|^8237 ≤ (8878298642521/25000000000000 : ℝ)^6189
        have hw : |(4593865049/10000000000 : ℝ)|=(4593865049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104812071/5000000000 : ℝ)*x 0 + (1305708731/2500000000 : ℝ)*x 1 + (679904803/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104812071/5000000000 : ℝ)^8237 ≤ (2681495155031/20000000000000 : ℝ)^6189 := by
    have hnat : (1104812071 : ℕ)^8237*20000000000000^6189 ≤ 2681495155031^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104812071 5000000000 2681495155031 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305708731/2500000000 : ℝ)^8237 ≤ (21063414204773/50000000000000 : ℝ)^6189 := by
    have hnat : (1305708731 : ℕ)^8237*50000000000000^6189 ≤ 21063414204773^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305708731 2500000000 21063414204773 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679904803/1250000000 : ℝ)^8237 ≤ (44465695800309/100000000000000 : ℝ)^6189 := by
    have hnat : (679904803 : ℕ)^8237*100000000000000^6189 ≤ 44465695800309^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679904803 1250000000 44465695800309 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104812071/5000000000 : ℝ), (1305708731/2500000000 : ℝ), (679904803/1250000000 : ℝ)] ![(2681495155031/20000000000000 : ℝ), (21063414204773/50000000000000 : ℝ), (44465695800309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104812071/5000000000 : ℝ)|^8237 ≤ (2681495155031/20000000000000 : ℝ)^6189
        have hw : |(-1104812071/5000000000 : ℝ)|=(1104812071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305708731/2500000000 : ℝ)|^8237 ≤ (21063414204773/50000000000000 : ℝ)^6189
        have hw : |(1305708731/2500000000 : ℝ)|=(1305708731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679904803/1250000000 : ℝ)|^8237 ≤ (44465695800309/100000000000000 : ℝ)^6189
        have hw : |(679904803/1250000000 : ℝ)|=(679904803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301388791/10000000000 : ℝ)*x 0 + (-420819783/2000000000 : ℝ)*x 1 + (5439239533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301388791/10000000000 : ℝ)^8237 ≤ (42972193734041/100000000000000 : ℝ)^6189 := by
    have hnat : (5301388791 : ℕ)^8237*100000000000000^6189 ≤ 42972193734041^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301388791 10000000000 42972193734041 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420819783/2000000000 : ℝ)^8237 ≤ (6281049194563/50000000000000 : ℝ)^6189 := by
    have hnat : (420819783 : ℕ)^8237*50000000000000^6189 ≤ 6281049194563^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420819783 2000000000 6281049194563 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439239533/10000000000 : ℝ)^8237 ≤ (8893141573283/20000000000000 : ℝ)^6189 := by
    have hnat : (5439239533 : ℕ)^8237*20000000000000^6189 ≤ 8893141573283^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439239533 10000000000 8893141573283 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301388791/10000000000 : ℝ), (-420819783/2000000000 : ℝ), (5439239533/10000000000 : ℝ)] ![(42972193734041/100000000000000 : ℝ), (6281049194563/50000000000000 : ℝ), (8893141573283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301388791/10000000000 : ℝ)|^8237 ≤ (42972193734041/100000000000000 : ℝ)^6189
        have hw : |(5301388791/10000000000 : ℝ)|=(5301388791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420819783/2000000000 : ℝ)|^8237 ≤ (6281049194563/50000000000000 : ℝ)^6189
        have hw : |(-420819783/2000000000 : ℝ)|=(420819783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439239533/10000000000 : ℝ)|^8237 ≤ (8893141573283/20000000000000 : ℝ)^6189
        have hw : |(5439239533/10000000000 : ℝ)|=(5439239533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662673587/1250000000 : ℝ)*x 0 + (1359809741/2500000000 : ℝ)*x 1 + (-2104099823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662673587/1250000000 : ℝ)^8237 ≤ (2685762044323/6250000000000 : ℝ)^6189 := by
    have hnat : (662673587 : ℕ)^8237*6250000000000^6189 ≤ 2685762044323^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662673587 1250000000 2685762044323 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359809741/2500000000 : ℝ)^8237 ≤ (111164254189/250000000000 : ℝ)^6189 := by
    have hnat : (1359809741 : ℕ)^8237*250000000000^6189 ≤ 111164254189^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359809741 2500000000 111164254189 250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104099823/10000000000 : ℝ)^8237 ≤ (12562105604029/100000000000000 : ℝ)^6189 := by
    have hnat : (2104099823 : ℕ)^8237*100000000000000^6189 ≤ 12562105604029^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104099823 10000000000 12562105604029 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662673587/1250000000 : ℝ), (1359809741/2500000000 : ℝ), (-2104099823/10000000000 : ℝ)] ![(2685762044323/6250000000000 : ℝ), (111164254189/250000000000 : ℝ), (12562105604029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662673587/1250000000 : ℝ)|^8237 ≤ (2685762044323/6250000000000 : ℝ)^6189
        have hw : |(662673587/1250000000 : ℝ)|=(662673587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359809741/2500000000 : ℝ)|^8237 ≤ (111164254189/250000000000 : ℝ)^6189
        have hw : |(1359809741/2500000000 : ℝ)|=(1359809741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104099823/10000000000 : ℝ)|^8237 ≤ (12562105604029/100000000000000 : ℝ)^6189
        have hw : |(-2104099823/10000000000 : ℝ)|=(2104099823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s3_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375728921/10000000000 : ℝ)*x 0 + (1148022823/2500000000 : ℝ)*x 1 + (2084909249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375728921/10000000000 : ℝ)^8237 ≤ (33286682665281/100000000000000 : ℝ)^6189 := by
    have hnat : (4375728921 : ℕ)^8237*100000000000000^6189 ≤ 33286682665281^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375728921 10000000000 33286682665281 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1148022823/2500000000 : ℝ)^8237 ≤ (4436868262471/12500000000000 : ℝ)^6189 := by
    have hnat : (1148022823 : ℕ)^8237*12500000000000^6189 ≤ 4436868262471^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148022823 2500000000 4436868262471 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084909249/5000000000 : ℝ)^8237 ≤ (15609185604809/50000000000000 : ℝ)^6189 := by
    have hnat : (2084909249 : ℕ)^8237*50000000000000^6189 ≤ 15609185604809^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084909249 5000000000 15609185604809 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375728921/10000000000 : ℝ), (1148022823/2500000000 : ℝ), (2084909249/5000000000 : ℝ)] ![(33286682665281/100000000000000 : ℝ), (4436868262471/12500000000000 : ℝ), (15609185604809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375728921/10000000000 : ℝ)|^8237 ≤ (33286682665281/100000000000000 : ℝ)^6189
        have hw : |(4375728921/10000000000 : ℝ)|=(4375728921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1148022823/2500000000 : ℝ)|^8237 ≤ (4436868262471/12500000000000 : ℝ)^6189
        have hw : |(1148022823/2500000000 : ℝ)|=(1148022823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084909249/5000000000 : ℝ)|^8237 ≤ (15609185604809/50000000000000 : ℝ)^6189
        have hw : |(2084909249/5000000000 : ℝ)|=(2084909249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5161/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14939/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8407/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8407/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8407/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8407/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8407/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8407/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4301/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (5194075853106311/100000000000000000000 : ℝ) := by
    have hpowers : (4301/50000 : ℝ)^2059 ≤ (5194075853106311/100000000000000000000 : ℝ)^512 := by
      have hnat : (4301 : ℕ)^2059*100000000000000000000^512 ≤ 5194075853106311^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4301 50000 5194075853106311 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4301/50000 : ℝ)) (X := (5194075853106311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8407/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (76921580425165883/100000000000000000000 : ℝ) := by
    have hpowers : (8407/50000 : ℝ)^2059 ≤ (76921580425165883/100000000000000000000 : ℝ)^512 := by
      have hnat : (8407 : ℕ)^2059*100000000000000000000^512 ≤ 76921580425165883^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8407 50000 76921580425165883 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8407/50000 : ℝ)) (X := (76921580425165883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005194075853106311/50000000000000000000 : ℝ) ≤ (10000258306271147/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50005194075853106311/50000000000000000000 : ℝ)^512 ≤ (10000258306271147/10000000000000000 : ℝ)^2059 := by
      have hnat : (50005194075853106311 : ℕ)^512*10000000000000000^2059 ≤ 10000258306271147^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005194075853106311 50000000000000000000 10000258306271147 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000258306271147/10000000000000000 : ℝ)) (X := (50005194075853106311/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50041057828139136097/50000000000000000000 : ℝ) ≤ (10002041294446311/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50041057828139136097/50000000000000000000 : ℝ)^512 ≤ (10002041294446311/10000000000000000 : ℝ)^2059 := by
      have hnat : (50041057828139136097 : ℕ)^512*10000000000000000^2059 ≤ 10002041294446311^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041057828139136097 50000000000000000000 10002041294446311 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002041294446311/10000000000000000 : ℝ)) (X := (50041057828139136097/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076921580425165883/50000000000000000000 : ℝ) ≤ (400152971304859/400000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50076921580425165883/50000000000000000000 : ℝ)^512 ≤ (400152971304859/400000000000000 : ℝ)^2059 := by
      have hnat : (50076921580425165883 : ℕ)^512*400000000000000^2059 ≤ 400152971304859^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076921580425165883 50000000000000000000 400152971304859 400000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400152971304859/400000000000000 : ℝ)) (X := (50076921580425165883/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5194075853106311/100000000000000000000 : ℝ) ≤ ((20522861670633284427/20530000000000000000 : ℝ)+2*(445747043791/205300000000000 : ℝ)*(4301/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (20522861670633284427/20530000000000000000 : ℝ)+2*(445747043791/205300000000000 : ℝ)*(4301/50000 : ℝ)=(10000258306271147/10000000000000000 : ℝ) by norm_num, show 1+2*(5194075853106311/100000000000000000000 : ℝ)=(50005194075853106311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76921580425165883/100000000000000000000 : ℝ)+(5194075853106311/100000000000000000000 : ℝ) ≤ ((20522861670633284427/20530000000000000000 : ℝ)+(445747043791/205300000000000 : ℝ)*((8407/50000 : ℝ)+(4301/50000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (20522861670633284427/20530000000000000000 : ℝ)+(445747043791/205300000000000 : ℝ)*((8407/50000 : ℝ)+(4301/50000 : ℝ))=(10002041294446311/10000000000000000 : ℝ) by norm_num, show 1+(76921580425165883/100000000000000000000 : ℝ)+(5194075853106311/100000000000000000000 : ℝ)=(50041057828139136097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76921580425165883/100000000000000000000 : ℝ) ≤ ((20522861670633284427/20530000000000000000 : ℝ)+2*(445747043791/205300000000000 : ℝ)*(8407/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (20522861670633284427/20530000000000000000 : ℝ)+2*(445747043791/205300000000000 : ℝ)*(8407/50000 : ℝ)=(400152971304859/400000000000000 : ℝ) by norm_num, show 1+2*(76921580425165883/100000000000000000000 : ℝ)=(50076921580425165883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20522861670633284427/20530000000000000000 : ℝ)*(X 1 0+X 2 0)+(445747043791/205300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (4301/50000 : ℝ)) (hi := (8407/50000 : ℝ)) (c := (20522861670633284427/20530000000000000000 : ℝ)) (alpha := (445747043791/205300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20522861670633284427/20530000000000000000 : ℝ)*(X 0 1+X 2 1)+(445747043791/205300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (4301/50000 : ℝ)) (hi := (8407/50000 : ℝ)) (c := (20522861670633284427/20530000000000000000 : ℝ)) (alpha := (445747043791/205300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20522861670633284427/20530000000000000000 : ℝ)*(X 0 2+X 1 2)+(445747043791/205300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (4301/50000 : ℝ)) (hi := (8407/50000 : ℝ)) (c := (20522861670633284427/20530000000000000000 : ℝ)) (alpha := (445747043791/205300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276200017/1250000000 : ℝ)*X 0 0+(2720077081/5000000000 : ℝ)*X 0 1+(652740601/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356264959/10000000000 : ℝ)*X 1 0+(-2321413849/10000000000 : ℝ)*X 1 1+(2610962467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267813249/500000000 : ℝ)*X 2 0+(5221925061/10000000000 : ℝ)*X 2 1+(-464282731/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375682781/10000000000 : ℝ)*X 0 0+(521004231/1250000000 : ℝ)*X 0 1+(4593865049/10000000000 : ℝ)*X 0 2+(4375682781/10000000000 : ℝ)*X 1 0+(521004231/1250000000 : ℝ)*X 1 1+(4593865049/10000000000 : ℝ)*X 1 2+(4375682781/10000000000 : ℝ)*X 2 0+(521004231/1250000000 : ℝ)*X 2 1+(4593865049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104812071/5000000000 : ℝ)*X 0 0+(1305708731/2500000000 : ℝ)*X 0 1+(679904803/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301388791/10000000000 : ℝ)*X 1 0+(-420819783/2000000000 : ℝ)*X 1 1+(5439239533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662673587/1250000000 : ℝ)*X 2 0+(1359809741/2500000000 : ℝ)*X 2 1+(-2104099823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375728921/10000000000 : ℝ)*X 0 0+(1148022823/2500000000 : ℝ)*X 0 1+(2084909249/5000000000 : ℝ)*X 0 2+(4375728921/10000000000 : ℝ)*X 1 0+(1148022823/2500000000 : ℝ)*X 1 1+(2084909249/5000000000 : ℝ)*X 1 2+(4375728921/10000000000 : ℝ)*X 2 0+(1148022823/2500000000 : ℝ)*X 2 1+(2084909249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574461428509086713410420263/256625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (363304921/50000000000000 : ℝ)*(base19) + (281599797/50000000000000 : ℝ)*(base23) + (97149827/100000000000000 : ℝ)*(lower2) + (6291107/25000000000000 : ℝ)*(upper3) + (2902947/4000000000000 : ℝ)*(upper5) + (1732681716470823/50000000000000 : ℝ)*(major0) + (1732681716470823/50000000000000 : ℝ)*(major1) + (1732681716470823/50000000000000 : ℝ)*(major2) + (4582349213697953/100000000000000 : ℝ)*(sp0) + (458236596197239/10000000000000 : ℝ)*(sp1) + (2291183062691319/50000000000000 : ℝ)*(sp2) + (469670832368753/20000000000000 : ℝ)*(sp3) + (17474884279/100000000000000 : ℝ)*(sp4) + (371302487/6250000000000 : ℝ)*(sp7) + (587090025670889/25000000000000 : ℝ)*(f.failure) + (572795836072779/12500000000000 : ℝ)*(f.sum) + (35892449752829/10265000000000000000000000000 : ℝ)*base66 + (1895271588706073421/1026500000000000000000000000000000 : ℝ)*base67 + (8262107128251426579/1026500000000000000000000000000000 : ℝ)*base70 + (7835309662430426579/1026500000000000000000000000000000 : ℝ)*base72 + (392210306459/160390625000000000000000000 : ℝ)*base73 + (7934364093661426579/1026500000000000000000000000000000 : ℝ)*base76 + (11876573676025426579/1026500000000000000000000000000000 : ℝ)*base78 + (2152116016797926579/1026500000000000000000000000000000 : ℝ)*base80 + (43659670792929/10265000000000000000000000000 : ℝ)*base82 + (22663639/2500000000000000000000 : ℝ)*base90 + (22663639/2500000000000000000000 : ℝ)*base92 + (22663639/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (463192835243471705307081249/51325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1231504071/50000000000000 : ℝ)*(base19) + (2312106017/100000000000000 : ℝ)*(base23) + (747169/4000000000000 : ℝ)*(upper2) + (423582593/100000000000000 : ℝ)*(upper3) + (174728340906043/5000000000000 : ℝ)*(major0) + (174728340906043/5000000000000 : ℝ)*(major1) + (174728340906043/5000000000000 : ℝ)*(major2) + (55781040637/100000000000000 : ℝ)*(sp1) + (45798652269/100000000000000 : ℝ)*(sp2) + (4164912861/100000000000000 : ℝ)*(sp3) + (577622885252541/12500000000000 : ℝ)*(sp4) + (4620924837971549/100000000000000 : ℝ)*(sp5) + (4620934971262043/100000000000000 : ℝ)*(sp6) + (1850114131629/78125000000 : ℝ)*(sp7) + (118407512669899/5000000000000 : ℝ)*(f.failure) + (577622885252541/12500000000000 : ℝ)*(f.sum) + (507689053353/2053000000000000000000000000 : ℝ)*base66 + (1046121074482607639/102650000000000000000000000000000 : ℝ)*base68 + (1009752054352257639/102650000000000000000000000000000 : ℝ)*base70 + (230640615769557639/102650000000000000000000000000000 : ℝ)*base72 + (1142569163001/256625000000000000000000000 : ℝ)*base74 + (400104106885207639/102650000000000000000000000000000 : ℝ)*base76 + (1020292103795457639/102650000000000000000000000000000 : ℝ)*base78 + (2329155926123457639/102650000000000000000000000000000 : ℝ)*base80 + (3979655737707/2053000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (739851/500000000000000000000 : ℝ)*base89 + (739851/500000000000000000000 : ℝ)*base91 + (739851/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1044_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5161/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14939/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s4_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-221349391/1000000000 : ℝ)*x 0 + (5407064981/10000000000 : ℝ)*x 1 + (5252471803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221349391/1000000000 : ℝ)^8237 ≤ (1679841962261/12500000000000 : ℝ)^6189 := by
    have hnat : (221349391 : ℕ)^8237*12500000000000^6189 ≤ 1679841962261^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221349391 1000000000 1679841962261 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407064981/10000000000 : ℝ)^8237 ≤ (5514498299217/12500000000000 : ℝ)^6189 := by
    have hnat : (5407064981 : ℕ)^8237*12500000000000^6189 ≤ 5514498299217^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407064981 10000000000 5514498299217 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252471803/10000000000 : ℝ)^8237 ≤ (10611319474429/25000000000000 : ℝ)^6189 := by
    have hnat : (5252471803 : ℕ)^8237*25000000000000^6189 ≤ 10611319474429^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252471803 10000000000 10611319474429 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221349391/1000000000 : ℝ), (5407064981/10000000000 : ℝ), (5252471803/10000000000 : ℝ)] ![(1679841962261/12500000000000 : ℝ), (5514498299217/12500000000000 : ℝ), (10611319474429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221349391/1000000000 : ℝ)|^8237 ≤ (1679841962261/12500000000000 : ℝ)^6189
        have hw : |(-221349391/1000000000 : ℝ)|=(221349391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407064981/10000000000 : ℝ)|^8237 ≤ (5514498299217/12500000000000 : ℝ)^6189
        have hw : |(5407064981/10000000000 : ℝ)|=(5407064981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252471803/10000000000 : ℝ)|^8237 ≤ (10611319474429/25000000000000 : ℝ)^6189
        have hw : |(5252471803/10000000000 : ℝ)|=(5252471803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337022503/2500000000 : ℝ)*x 0 + (-2292145877/10000000000 : ℝ)*x 1 + (5252471821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337022503/2500000000 : ℝ)^8237 ≤ (5434593224883/12500000000000 : ℝ)^6189 := by
    have hnat : (1337022503 : ℕ)^8237*12500000000000^6189 ≤ 5434593224883^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337022503 2500000000 5434593224883 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292145877/10000000000 : ℝ)^8237 ≤ (3519494023891/25000000000000 : ℝ)^6189 := by
    have hnat : (2292145877 : ℕ)^8237*25000000000000^6189 ≤ 3519494023891^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292145877 10000000000 3519494023891 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252471821/10000000000 : ℝ)^8237 ≤ (42445278091307/100000000000000 : ℝ)^6189 := by
    have hnat : (5252471821 : ℕ)^8237*100000000000000^6189 ≤ 42445278091307^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252471821 10000000000 42445278091307 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337022503/2500000000 : ℝ), (-2292145877/10000000000 : ℝ), (5252471821/10000000000 : ℝ)] ![(5434593224883/12500000000000 : ℝ), (3519494023891/25000000000000 : ℝ), (42445278091307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337022503/2500000000 : ℝ)|^8237 ≤ (5434593224883/12500000000000 : ℝ)^6189
        have hw : |(1337022503/2500000000 : ℝ)|=(1337022503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2292145877/10000000000 : ℝ)|^8237 ≤ (3519494023891/25000000000000 : ℝ)^6189
        have hw : |(-2292145877/10000000000 : ℝ)|=(2292145877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252471821/10000000000 : ℝ)|^8237 ≤ (42445278091307/100000000000000 : ℝ)^6189
        have hw : |(5252471821/10000000000 : ℝ)|=(5252471821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106961801/200000000 : ℝ)*x 0 + (5252471757/10000000000 : ℝ)*x 1 + (-229214591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106961801/200000000 : ℝ)^8237 ≤ (10869186552551/25000000000000 : ℝ)^6189 := by
    have hnat : (106961801 : ℕ)^8237*25000000000000^6189 ≤ 10869186552551^6189*200000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106961801 200000000 10869186552551 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252471757/10000000000 : ℝ)^8237 ≤ (42445277402981/100000000000000 : ℝ)^6189 := by
    have hnat : (5252471757 : ℕ)^8237*100000000000000^6189 ≤ 42445277402981^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252471757 10000000000 42445277402981 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229214591/1000000000 : ℝ)^8237 ≤ (14077976365313/100000000000000 : ℝ)^6189 := by
    have hnat : (229214591 : ℕ)^8237*100000000000000^6189 ≤ 14077976365313^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229214591 1000000000 14077976365313 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106961801/200000000 : ℝ), (5252471757/10000000000 : ℝ), (-229214591/1000000000 : ℝ)] ![(10869186552551/25000000000000 : ℝ), (42445277402981/100000000000000 : ℝ), (14077976365313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106961801/200000000 : ℝ)|^8237 ≤ (10869186552551/25000000000000 : ℝ)^6189
        have hw : |(106961801/200000000 : ℝ)|=(106961801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252471757/10000000000 : ℝ)|^8237 ≤ (42445277402981/100000000000000 : ℝ)^6189
        have hw : |(5252471757/10000000000 : ℝ)|=(5252471757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229214591/1000000000 : ℝ)|^8237 ≤ (14077976365313/100000000000000 : ℝ)^6189
        have hw : |(-229214591/1000000000 : ℝ)|=(229214591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (175119989/400000000 : ℝ)*x 0 + (4229815247/10000000000 : ℝ)*x 1 + (181258949/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175119989/400000000 : ℝ)^8237 ≤ (16654837567531/50000000000000 : ℝ)^6189 := by
    have hnat : (175119989 : ℕ)^8237*50000000000000^6189 ≤ 16654837567531^6189*400000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175119989 400000000 16654837567531 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229815247/10000000000 : ℝ)^8237 ≤ (7954402100811/25000000000000 : ℝ)^6189 := by
    have hnat : (4229815247 : ℕ)^8237*25000000000000^6189 ≤ 7954402100811^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229815247 10000000000 7954402100811 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181258949/400000000 : ℝ)^8237 ≤ (8718179109903/25000000000000 : ℝ)^6189 := by
    have hnat : (181258949 : ℕ)^8237*25000000000000^6189 ≤ 8718179109903^6189*400000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181258949 400000000 8718179109903 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175119989/400000000 : ℝ), (4229815247/10000000000 : ℝ), (181258949/400000000 : ℝ)] ![(16654837567531/50000000000000 : ℝ), (7954402100811/25000000000000 : ℝ), (8718179109903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175119989/400000000 : ℝ)|^8237 ≤ (16654837567531/50000000000000 : ℝ)^6189
        have hw : |(175119989/400000000 : ℝ)|=(175119989/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229815247/10000000000 : ℝ)|^8237 ≤ (7954402100811/25000000000000 : ℝ)^6189
        have hw : |(4229815247/10000000000 : ℝ)|=(4229815247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181258949/400000000 : ℝ)|^8237 ≤ (8718179109903/25000000000000 : ℝ)^6189
        have hw : |(181258949/400000000 : ℝ)|=(181258949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106751287/5000000000 : ℝ)*x 0 + (1313232193/2500000000 : ℝ)*x 1 + (5406605917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106751287/5000000000 : ℝ)^8237 ≤ (6719402853021/50000000000000 : ℝ)^6189 := by
    have hnat : (1106751287 : ℕ)^8237*50000000000000^6189 ≤ 6719402853021^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106751287 5000000000 6719402853021 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313232193/2500000000 : ℝ)^8237 ≤ (5306274089161/12500000000000 : ℝ)^6189 := by
    have hnat : (1313232193 : ℕ)^8237*12500000000000^6189 ≤ 5306274089161^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313232193 2500000000 5306274089161 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406605917/10000000000 : ℝ)^8237 ≤ (882220031327/2000000000000 : ℝ)^6189 := by
    have hnat : (5406605917 : ℕ)^8237*2000000000000^6189 ≤ 882220031327^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406605917 10000000000 882220031327 2000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106751287/5000000000 : ℝ), (1313232193/2500000000 : ℝ), (5406605917/10000000000 : ℝ)] ![(6719402853021/50000000000000 : ℝ), (5306274089161/12500000000000 : ℝ), (882220031327/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106751287/5000000000 : ℝ)|^8237 ≤ (6719402853021/50000000000000 : ℝ)^6189
        have hw : |(-1106751287/5000000000 : ℝ)|=(1106751287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313232193/2500000000 : ℝ)|^8237 ≤ (5306274089161/12500000000000 : ℝ)^6189
        have hw : |(1313232193/2500000000 : ℝ)|=(1313232193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406605917/10000000000 : ℝ)|^8237 ≤ (882220031327/2000000000000 : ℝ)^6189
        have hw : |(5406605917/10000000000 : ℝ)|=(5406605917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327305381/2500000000 : ℝ)*x 0 + (-267251479/1250000000 : ℝ)*x 1 + (5406605863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327305381/2500000000 : ℝ)^8237 ≤ (2691044686293/6250000000000 : ℝ)^6189 := by
    have hnat : (1327305381 : ℕ)^8237*6250000000000^6189 ≤ 2691044686293^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327305381 2500000000 2691044686293 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267251479/1250000000 : ℝ)^8237 ≤ (12832284019133/100000000000000 : ℝ)^6189 := by
    have hnat : (267251479 : ℕ)^8237*100000000000000^6189 ≤ 12832284019133^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267251479 1250000000 12832284019133 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406605863/10000000000 : ℝ)^8237 ≤ (4411100097999/10000000000000 : ℝ)^6189 := by
    have hnat : (5406605863 : ℕ)^8237*10000000000000^6189 ≤ 4411100097999^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406605863 10000000000 4411100097999 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327305381/2500000000 : ℝ), (-267251479/1250000000 : ℝ), (5406605863/10000000000 : ℝ)] ![(2691044686293/6250000000000 : ℝ), (12832284019133/100000000000000 : ℝ), (4411100097999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327305381/2500000000 : ℝ)|^8237 ≤ (2691044686293/6250000000000 : ℝ)^6189
        have hw : |(1327305381/2500000000 : ℝ)|=(1327305381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267251479/1250000000 : ℝ)|^8237 ≤ (12832284019133/100000000000000 : ℝ)^6189
        have hw : |(-267251479/1250000000 : ℝ)|=(267251479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406605863/10000000000 : ℝ)|^8237 ≤ (4411100097999/10000000000000 : ℝ)^6189
        have hw : |(5406605863/10000000000 : ℝ)|=(5406605863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132730537/250000000 : ℝ)*x 0 + (2703302943/5000000000 : ℝ)*x 1 + (-2138011861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132730537/250000000 : ℝ)^8237 ≤ (21528357252889/50000000000000 : ℝ)^6189 := by
    have hnat : (132730537 : ℕ)^8237*50000000000000^6189 ≤ 21528357252889^6189*250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132730537 250000000 21528357252889 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703302943/5000000000 : ℝ)^8237 ≤ (5513875153717/12500000000000 : ℝ)^6189 := by
    have hnat : (2703302943 : ℕ)^8237*12500000000000^6189 ≤ 5513875153717^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703302943 5000000000 5513875153717 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138011861/10000000000 : ℝ)^8237 ≤ (12832284250787/100000000000000 : ℝ)^6189 := by
    have hnat : (2138011861 : ℕ)^8237*100000000000000^6189 ≤ 12832284250787^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138011861 10000000000 12832284250787 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132730537/250000000 : ℝ), (2703302943/5000000000 : ℝ), (-2138011861/10000000000 : ℝ)] ![(21528357252889/50000000000000 : ℝ), (5513875153717/12500000000000 : ℝ), (12832284250787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132730537/250000000 : ℝ)|^8237 ≤ (21528357252889/50000000000000 : ℝ)^6189
        have hw : |(132730537/250000000 : ℝ)|=(132730537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703302943/5000000000 : ℝ)|^8237 ≤ (5513875153717/12500000000000 : ℝ)^6189
        have hw : |(2703302943/5000000000 : ℝ)|=(2703302943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138011861/10000000000 : ℝ)|^8237 ≤ (12832284250787/100000000000000 : ℝ)^6189
        have hw : |(-2138011861/10000000000 : ℝ)|=(2138011861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s4_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378016227/10000000000 : ℝ)*x 0 + (4530581323/10000000000 : ℝ)*x 1 + (2115355737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378016227/10000000000 : ℝ)^8237 ≤ (8327460559117/25000000000000 : ℝ)^6189 := by
    have hnat : (4378016227 : ℕ)^8237*25000000000000^6189 ≤ 8327460559117^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378016227 10000000000 8327460559117 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530581323/10000000000 : ℝ)^8237 ≤ (34863576543093/100000000000000 : ℝ)^6189 := by
    have hnat : (4530581323 : ℕ)^8237*100000000000000^6189 ≤ 34863576543093^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530581323 10000000000 34863576543093 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115355737/5000000000 : ℝ)^8237 ≤ (3978322650347/12500000000000 : ℝ)^6189 := by
    have hnat : (2115355737 : ℕ)^8237*12500000000000^6189 ≤ 3978322650347^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115355737 5000000000 3978322650347 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378016227/10000000000 : ℝ), (4530581323/10000000000 : ℝ), (2115355737/5000000000 : ℝ)] ![(8327460559117/25000000000000 : ℝ), (34863576543093/100000000000000 : ℝ), (3978322650347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378016227/10000000000 : ℝ)|^8237 ≤ (8327460559117/25000000000000 : ℝ)^6189
        have hw : |(4378016227/10000000000 : ℝ)|=(4378016227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530581323/10000000000 : ℝ)|^8237 ≤ (34863576543093/100000000000000 : ℝ)^6189
        have hw : |(4530581323/10000000000 : ℝ)|=(4530581323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115355737/5000000000 : ℝ)|^8237 ≤ (3978322650347/12500000000000 : ℝ)^6189
        have hw : |(2115355737/5000000000 : ℝ)|=(2115355737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5161/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5161/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5161/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5161/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5161/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5161/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5161/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5161/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (10811022015719519/100000000000000000000 : ℝ) := by
    have hpowers : (5161/50000 : ℝ)^2059 ≤ (10811022015719519/100000000000000000000 : ℝ)^512 := by
      have hnat : (5161 : ℕ)^2059*100000000000000000000^512 ≤ 10811022015719519^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5161 50000 10811022015719519 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5161/50000 : ℝ)) (X := (10811022015719519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14939/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (373539861541327/781250000000000000 : ℝ) := by
    have hpowers : (14939/100000 : ℝ)^2059 ≤ (373539861541327/781250000000000000 : ℝ)^512 := by
      have hnat : (14939 : ℕ)^2059*781250000000000000^512 ≤ 373539861541327^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14939 100000 373539861541327 781250000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14939/100000 : ℝ)) (X := (373539861541327/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010811022015719519/50000000000000000000 : ℝ) ≤ (10000537619593713/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50010811022015719519/50000000000000000000 : ℝ)^512 ≤ (10000537619593713/10000000000000000 : ℝ)^2059 := by
      have hnat : (50010811022015719519 : ℕ)^512*10000000000000000^2059 ≤ 10000537619593713^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010811022015719519 50000000000000000000 10000537619593713 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537619593713/10000000000000000 : ℝ)) (X := (50010811022015719519/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (32018759719773763/32000000000000000 : ℝ) ≤ (1250182181541499/1250000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (32018759719773763/32000000000000000 : ℝ)^512 ≤ (1250182181541499/1250000000000000 : ℝ)^2059 := by
      have hnat : (32018759719773763 : ℕ)^512*1250000000000000^2059 ≤ 1250182181541499^2059*32000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32018759719773763 32000000000000000 1250182181541499 1250000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250182181541499/1250000000000000 : ℝ)) (X := (32018759719773763/32000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (390998539861541327/390625000000000000 : ℝ) ≤ (10002377285070271/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (390998539861541327/390625000000000000 : ℝ)^512 ≤ (10002377285070271/10000000000000000 : ℝ)^2059 := by
      have hnat : (390998539861541327 : ℕ)^512*10000000000000000^2059 ≤ 10002377285070271^2059*390625000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390998539861541327 390625000000000000 10002377285070271 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002377285070271/10000000000000000 : ℝ)) (X := (390998539861541327/390625000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10811022015719519/100000000000000000000 : ℝ) ≤ ((9230698632523028249/9234000000000000000 : ℝ)+2*(919832738279/461700000000000 : ℝ)*(5161/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (9230698632523028249/9234000000000000000 : ℝ)+2*(919832738279/461700000000000 : ℝ)*(5161/50000 : ℝ)=(10000537619593713/10000000000000000 : ℝ) by norm_num, show 1+2*(10811022015719519/100000000000000000000 : ℝ)=(50010811022015719519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(373539861541327/781250000000000000 : ℝ)+(10811022015719519/100000000000000000000 : ℝ) ≤ ((9230698632523028249/9234000000000000000 : ℝ)+(919832738279/461700000000000 : ℝ)*((14939/100000 : ℝ)+(5161/50000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (9230698632523028249/9234000000000000000 : ℝ)+(919832738279/461700000000000 : ℝ)*((14939/100000 : ℝ)+(5161/50000 : ℝ))=(1250182181541499/1250000000000000 : ℝ) by norm_num, show 1+(373539861541327/781250000000000000 : ℝ)+(10811022015719519/100000000000000000000 : ℝ)=(32018759719773763/32000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(373539861541327/781250000000000000 : ℝ) ≤ ((9230698632523028249/9234000000000000000 : ℝ)+2*(919832738279/461700000000000 : ℝ)*(14939/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (9230698632523028249/9234000000000000000 : ℝ)+2*(919832738279/461700000000000 : ℝ)*(14939/100000 : ℝ)=(10002377285070271/10000000000000000 : ℝ) by norm_num, show 1+2*(373539861541327/781250000000000000 : ℝ)=(390998539861541327/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9230698632523028249/9234000000000000000 : ℝ)*(X 1 0+X 2 0)+(919832738279/461700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5161/50000 : ℝ)) (hi := (14939/100000 : ℝ)) (c := (9230698632523028249/9234000000000000000 : ℝ)) (alpha := (919832738279/461700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9230698632523028249/9234000000000000000 : ℝ)*(X 0 1+X 2 1)+(919832738279/461700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5161/50000 : ℝ)) (hi := (14939/100000 : ℝ)) (c := (9230698632523028249/9234000000000000000 : ℝ)) (alpha := (919832738279/461700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9230698632523028249/9234000000000000000 : ℝ)*(X 0 2+X 1 2)+(919832738279/461700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5161/50000 : ℝ)) (hi := (14939/100000 : ℝ)) (c := (9230698632523028249/9234000000000000000 : ℝ)) (alpha := (919832738279/461700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-221349391/1000000000 : ℝ)*X 0 0+(5407064981/10000000000 : ℝ)*X 0 1+(5252471803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337022503/2500000000 : ℝ)*X 1 0+(-2292145877/10000000000 : ℝ)*X 1 1+(5252471821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106961801/200000000 : ℝ)*X 2 0+(5252471757/10000000000 : ℝ)*X 2 1+(-229214591/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((175119989/400000000 : ℝ)*X 0 0+(4229815247/10000000000 : ℝ)*X 0 1+(181258949/400000000 : ℝ)*X 0 2+(175119989/400000000 : ℝ)*X 1 0+(4229815247/10000000000 : ℝ)*X 1 1+(181258949/400000000 : ℝ)*X 1 2+(175119989/400000000 : ℝ)*X 2 0+(4229815247/10000000000 : ℝ)*X 2 1+(181258949/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106751287/5000000000 : ℝ)*X 0 0+(1313232193/2500000000 : ℝ)*X 0 1+(5406605917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327305381/2500000000 : ℝ)*X 1 0+(-267251479/1250000000 : ℝ)*X 1 1+(5406605863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132730537/250000000 : ℝ)*X 2 0+(2703302943/5000000000 : ℝ)*X 2 1+(-2138011861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378016227/10000000000 : ℝ)*X 0 0+(4530581323/10000000000 : ℝ)*X 0 1+(2115355737/5000000000 : ℝ)*X 0 2+(4378016227/10000000000 : ℝ)*X 1 0+(4530581323/10000000000 : ℝ)*X 1 1+(2115355737/5000000000 : ℝ)*X 1 2+(4378016227/10000000000 : ℝ)*X 2 0+(4530581323/10000000000 : ℝ)*X 2 1+(2115355737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199496787260476626805184471/30780000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1390840153/100000000000000 : ℝ)*(base19) + (684801079/50000000000000 : ℝ)*(base23) + (35939153/100000000000000 : ℝ)*(lower2) + (194909609/100000000000000 : ℝ)*(upper3) + (107928317/100000000000000 : ℝ)*(upper5) + (978369543630907/20000000000000 : ℝ)*(major0) + (978369543630907/20000000000000 : ℝ)*(major1) + (978369543630907/20000000000000 : ℝ)*(major2) + (129372476092137/2000000000000 : ℝ)*(sp0) + (3234326681694263/50000000000000 : ℝ)*(sp1) + (6468653384626521/100000000000000 : ℝ)*(sp2) + (103594460290057/3125000000000 : ℝ)*(sp3) + (3094962183/10000000000000 : ℝ)*(sp4) + (17736752651/100000000000000 : ℝ)*(sp7) + (828760116508619/25000000000000 : ℝ)*(f.failure) + (6468654754228679/100000000000000 : ℝ)*(f.sum) + (4692485040379/1154250000000000000000000000 : ℝ)*base66 + (387956674889357281/61560000000000000000000000000000 : ℝ)*base67 + (515423412761477281/61560000000000000000000000000000 : ℝ)*base69 + (598692063207677281/61560000000000000000000000000000 : ℝ)*base71 + (1191183358517/461700000000000000000000000 : ℝ)*base73 + (2376153998391317281/61560000000000000000000000000000 : ℝ)*base75 + (133900905496397281/61560000000000000000000000000000 : ℝ)*base77 + (935123206201637281/61560000000000000000000000000000 : ℝ)*base79 + (4702397799193/923400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1618869/2500000000000000000000 : ℝ)*base90 + (1618869/2500000000000000000000 : ℝ)*base92 + (1618869/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (726493656164980153891/307800000000000000000000000 : ℝ) := by norm_num
    linear_combination (145431893/20000000000000 : ℝ)*(base19) + (883506897/100000000000000 : ℝ)*(base23) + (129298421/100000000000000 : ℝ)*(upper2) + (261078441/100000000000000 : ℝ)*(upper5) + (492096784807699/10000000000000 : ℝ)*(major0) + (492096784807699/10000000000000 : ℝ)*(major1) + (492096784807699/10000000000000 : ℝ)*(major2) + (613998927/20000000000000 : ℝ)*(sp0) + (2246054253/10000000000000 : ℝ)*(sp1) + (17917338529/100000000000000 : ℝ)*(sp2) + (1626789587504597/25000000000000 : ℝ)*(sp4) + (6507138232311027/100000000000000 : ℝ)*(sp5) + (6507142619167597/100000000000000 : ℝ)*(sp6) + (3334774197465007/100000000000000 : ℝ)*(sp7) + (3334774197465007/100000000000000 : ℝ)*(f.failure) + (6507161420013023/100000000000000 : ℝ)*(f.sum) + (1755520490383/4617000000000000000000000000 : ℝ)*base65 + (12743411594256983/30780000000000000000000000000000 : ℝ)*base68 + (6213997468116983/30780000000000000000000000000000 : ℝ)*base70 + (136021765231043017/30780000000000000000000000000000 : ℝ)*base71 + (5969091832063/4617000000000000000000000000 : ℝ)*base73 + (40066203242483017/30780000000000000000000000000000 : ℝ)*base75 + (150372493859483017/30780000000000000000000000000000 : ℝ)*base77 + (342719321954976983/30780000000000000000000000000000 : ℝ)*base80 + (888644324209/923400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (73258257/10000000000000000000000 : ℝ)*base90 + (73258257/10000000000000000000000 : ℝ)*base92 + (73258257/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1044_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5161/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s5_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88575719/400000000 : ℝ)*x 0 + (5397638921/10000000000 : ℝ)*x 1 + (5261308059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88575719/400000000 : ℝ)^8237 ≤ (2689200184181/20000000000000 : ℝ)^6189 := by
    have hnat : (88575719 : ℕ)^8237*20000000000000^6189 ≤ 2689200184181^6189*400000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88575719 400000000 2689200184181 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397638921/10000000000 : ℝ)^8237 ≤ (11003414988977/25000000000000 : ℝ)^6189 := by
    have hnat : (5397638921 : ℕ)^8237*25000000000000^6189 ≤ 11003414988977^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397638921 10000000000 11003414988977 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261308059/10000000000 : ℝ)^8237 ≤ (21270169554767/50000000000000 : ℝ)^6189 := by
    have hnat : (5261308059 : ℕ)^8237*50000000000000^6189 ≤ 21270169554767^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261308059 10000000000 21270169554767 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88575719/400000000 : ℝ), (5397638921/10000000000 : ℝ), (5261308059/10000000000 : ℝ)] ![(2689200184181/20000000000000 : ℝ), (11003414988977/25000000000000 : ℝ), (21270169554767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88575719/400000000 : ℝ)|^8237 ≤ (2689200184181/20000000000000 : ℝ)^6189
        have hw : |(-88575719/400000000 : ℝ)|=(88575719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397638921/10000000000 : ℝ)|^8237 ≤ (11003414988977/25000000000000 : ℝ)^6189
        have hw : |(5397638921/10000000000 : ℝ)|=(5397638921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261308059/10000000000 : ℝ)|^8237 ≤ (21270169554767/50000000000000 : ℝ)^6189
        have hw : |(5261308059/10000000000 : ℝ)|=(5261308059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336436653/2500000000 : ℝ)*x 0 + (-2283612717/10000000000 : ℝ)*x 1 + (2630654053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336436653/2500000000 : ℝ)^8237 ≤ (1357856038681/3125000000000 : ℝ)^6189 := by
    have hnat : (1336436653 : ℕ)^8237*3125000000000^6189 ≤ 1357856038681^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336436653 2500000000 1357856038681 3125000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283612717/10000000000 : ℝ)^8237 ≤ (7004133565467/50000000000000 : ℝ)^6189 := by
    have hnat : (2283612717 : ℕ)^8237*50000000000000^6189 ≤ 7004133565467^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283612717 10000000000 7004133565467 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630654053/5000000000 : ℝ)^8237 ≤ (8508067923061/20000000000000 : ℝ)^6189 := by
    have hnat : (2630654053 : ℕ)^8237*20000000000000^6189 ≤ 8508067923061^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630654053 5000000000 8508067923061 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336436653/2500000000 : ℝ), (-2283612717/10000000000 : ℝ), (2630654053/5000000000 : ℝ)] ![(1357856038681/3125000000000 : ℝ), (7004133565467/50000000000000 : ℝ), (8508067923061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336436653/2500000000 : ℝ)|^8237 ≤ (1357856038681/3125000000000 : ℝ)^6189
        have hw : |(1336436653/2500000000 : ℝ)|=(1336436653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2283612717/10000000000 : ℝ)|^8237 ≤ (7004133565467/50000000000000 : ℝ)^6189
        have hw : |(-2283612717/10000000000 : ℝ)|=(2283612717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630654053/5000000000 : ℝ)|^8237 ≤ (8508067923061/20000000000000 : ℝ)^6189
        have hw : |(2630654053/5000000000 : ℝ)|=(2630654053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672873303/5000000000 : ℝ)*x 0 + (5261308071/10000000000 : ℝ)*x 1 + (-2283612771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672873303/5000000000 : ℝ)^8237 ≤ (10862848293221/25000000000000 : ℝ)^6189 := by
    have hnat : (2672873303 : ℕ)^8237*25000000000000^6189 ≤ 10862848293221^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672873303 5000000000 10862848293221 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261308071/10000000000 : ℝ)^8237 ≤ (42540339238667/100000000000000 : ℝ)^6189 := by
    have hnat : (5261308071 : ℕ)^8237*100000000000000^6189 ≤ 42540339238667^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261308071 10000000000 42540339238667 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283612771/10000000000 : ℝ)^8237 ≤ (14008267571797/100000000000000 : ℝ)^6189 := by
    have hnat : (2283612771 : ℕ)^8237*100000000000000^6189 ≤ 14008267571797^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283612771 10000000000 14008267571797 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672873303/5000000000 : ℝ), (5261308071/10000000000 : ℝ), (-2283612771/10000000000 : ℝ)] ![(10862848293221/25000000000000 : ℝ), (42540339238667/100000000000000 : ℝ), (14008267571797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672873303/5000000000 : ℝ)|^8237 ≤ (10862848293221/25000000000000 : ℝ)^6189
        have hw : |(2672873303/5000000000 : ℝ)|=(2672873303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261308071/10000000000 : ℝ)|^8237 ≤ (42540339238667/100000000000000 : ℝ)^6189
        have hw : |(5261308071/10000000000 : ℝ)|=(5261308071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283612771/10000000000 : ℝ)|^8237 ≤ (14008267571797/100000000000000 : ℝ)^6189
        have hw : |(-2283612771/10000000000 : ℝ)|=(2283612771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547314847/1250000000 : ℝ)*x 0 + (424756447/1000000000 : ℝ)*x 1 + (902717527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547314847/1250000000 : ℝ)^8237 ≤ (33314931213061/100000000000000 : ℝ)^6189 := by
    have hnat : (547314847 : ℕ)^8237*100000000000000^6189 ≤ 33314931213061^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547314847 1250000000 33314931213061 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424756447/1000000000 : ℝ)^8237 ≤ (7998856547563/25000000000000 : ℝ)^6189 := by
    have hnat : (424756447 : ℕ)^8237*25000000000000^6189 ≤ 7998856547563^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424756447 1000000000 7998856547563 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902717527/2000000000 : ℝ)^8237 ≤ (3468964257791/10000000000000 : ℝ)^6189 := by
    have hnat : (902717527 : ℕ)^8237*10000000000000^6189 ≤ 3468964257791^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902717527 2000000000 3468964257791 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547314847/1250000000 : ℝ), (424756447/1000000000 : ℝ), (902717527/2000000000 : ℝ)] ![(33314931213061/100000000000000 : ℝ), (7998856547563/25000000000000 : ℝ), (3468964257791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547314847/1250000000 : ℝ)|^8237 ≤ (33314931213061/100000000000000 : ℝ)^6189
        have hw : |(547314847/1250000000 : ℝ)|=(547314847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424756447/1000000000 : ℝ)|^8237 ≤ (7998856547563/25000000000000 : ℝ)^6189
        have hw : |(424756447/1000000000 : ℝ)|=(424756447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902717527/2000000000 : ℝ)|^8237 ≤ (3468964257791/10000000000000 : ℝ)^6189
        have hw : |(902717527/2000000000 : ℝ)|=(902717527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-221439853/1000000000 : ℝ)*x 0 + (5261663887/10000000000 : ℝ)*x 1 + (1349320487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221439853/1000000000 : ℝ)^8237 ≤ (1680755726643/12500000000000 : ℝ)^6189 := by
    have hnat : (221439853 : ℕ)^8237*12500000000000^6189 ≤ 1680755726643^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221439853 1000000000 1680755726643 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261663887/10000000000 : ℝ)^8237 ≤ (21272084122711/50000000000000 : ℝ)^6189 := by
    have hnat : (5261663887 : ℕ)^8237*50000000000000^6189 ≤ 21272084122711^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261663887 10000000000 21272084122711 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349320487/2500000000 : ℝ)^8237 ≤ (22004892963509/50000000000000 : ℝ)^6189 := by
    have hnat : (1349320487 : ℕ)^8237*50000000000000^6189 ≤ 22004892963509^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349320487 2500000000 22004892963509 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221439853/1000000000 : ℝ), (5261663887/10000000000 : ℝ), (1349320487/2500000000 : ℝ)] ![(1680755726643/12500000000000 : ℝ), (21272084122711/50000000000000 : ℝ), (22004892963509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221439853/1000000000 : ℝ)|^8237 ≤ (1680755726643/12500000000000 : ℝ)^6189
        have hw : |(-221439853/1000000000 : ℝ)|=(221439853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261663887/10000000000 : ℝ)|^8237 ≤ (21272084122711/50000000000000 : ℝ)^6189
        have hw : |(5261663887/10000000000 : ℝ)|=(5261663887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349320487/2500000000 : ℝ)|^8237 ≤ (22004892963509/50000000000000 : ℝ)^6189
        have hw : |(1349320487/2500000000 : ℝ)|=(1349320487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062293761/2000000000 : ℝ)*x 0 + (-1677843/7812500 : ℝ)*x 1 + (5397281707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062293761/2000000000 : ℝ)^8237 ≤ (43080972501927/100000000000000 : ℝ)^6189 := by
    have hnat : (1062293761 : ℕ)^8237*100000000000000^6189 ≤ 43080972501927^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062293761 2000000000 43080972501927 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1677843/7812500 : ℝ)^8237 ≤ (3227311042581/25000000000000 : ℝ)^6189 := by
    have hnat : (1677843 : ℕ)^8237*25000000000000^6189 ≤ 3227311042581^6189*7812500^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677843 7812500 3227311042581 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397281707/10000000000 : ℝ)^8237 ≤ (5501222913951/12500000000000 : ℝ)^6189 := by
    have hnat : (5397281707 : ℕ)^8237*12500000000000^6189 ≤ 5501222913951^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397281707 10000000000 5501222913951 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062293761/2000000000 : ℝ), (-1677843/7812500 : ℝ), (5397281707/10000000000 : ℝ)] ![(43080972501927/100000000000000 : ℝ), (3227311042581/25000000000000 : ℝ), (5501222913951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062293761/2000000000 : ℝ)|^8237 ≤ (43080972501927/100000000000000 : ℝ)^6189
        have hw : |(1062293761/2000000000 : ℝ)|=(1062293761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1677843/7812500 : ℝ)|^8237 ≤ (3227311042581/25000000000000 : ℝ)^6189
        have hw : |(-1677843/7812500 : ℝ)|=(1677843/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397281707/10000000000 : ℝ)|^8237 ≤ (5501222913951/12500000000000 : ℝ)^6189
        have hw : |(5397281707/10000000000 : ℝ)|=(5397281707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327867177/2500000000 : ℝ)*x 0 + (1349320431/2500000000 : ℝ)*x 1 + (-536909787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327867177/2500000000 : ℝ)^8237 ≤ (2154048572741/5000000000000 : ℝ)^6189 := by
    have hnat : (1327867177 : ℕ)^8237*5000000000000^6189 ≤ 2154048572741^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327867177 2500000000 2154048572741 5000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349320431/2500000000 : ℝ)^8237 ≤ (44009783496097/100000000000000 : ℝ)^6189 := by
    have hnat : (1349320431 : ℕ)^8237*100000000000000^6189 ≤ 44009783496097^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349320431 2500000000 44009783496097 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536909787/2500000000 : ℝ)^8237 ≤ (12909245034321/100000000000000 : ℝ)^6189 := by
    have hnat : (536909787 : ℕ)^8237*100000000000000^6189 ≤ 12909245034321^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536909787 2500000000 12909245034321 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327867177/2500000000 : ℝ), (1349320431/2500000000 : ℝ), (-536909787/2500000000 : ℝ)] ![(2154048572741/5000000000000 : ℝ), (44009783496097/100000000000000 : ℝ), (12909245034321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327867177/2500000000 : ℝ)|^8237 ≤ (2154048572741/5000000000000 : ℝ)^6189
        have hw : |(1327867177/2500000000 : ℝ)|=(1327867177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349320431/2500000000 : ℝ)|^8237 ≤ (44009783496097/100000000000000 : ℝ)^6189
        have hw : |(1349320431/2500000000 : ℝ)|=(1349320431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536909787/2500000000 : ℝ)|^8237 ≤ (12909245034321/100000000000000 : ℝ)^6189
        have hw : |(-536909787/2500000000 : ℝ)|=(536909787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s5_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378529703/10000000000 : ℝ)*x 0 + (4512893477/10000000000 : ℝ)*x 1 + (4248261649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378529703/10000000000 : ℝ)^8237 ≤ (33315041865607/100000000000000 : ℝ)^6189 := by
    have hnat : (4378529703 : ℕ)^8237*100000000000000^6189 ≤ 33315041865607^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378529703 10000000000 33315041865607 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512893477/10000000000 : ℝ)^8237 ≤ (17341271162561/50000000000000 : ℝ)^6189 := by
    have hnat : (4512893477 : ℕ)^8237*50000000000000^6189 ≤ 17341271162561^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512893477 10000000000 17341271162561 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248261649/10000000000 : ℝ)^8237 ≤ (1600120789731/5000000000000 : ℝ)^6189 := by
    have hnat : (4248261649 : ℕ)^8237*5000000000000^6189 ≤ 1600120789731^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248261649 10000000000 1600120789731 5000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378529703/10000000000 : ℝ), (4512893477/10000000000 : ℝ), (4248261649/10000000000 : ℝ)] ![(33315041865607/100000000000000 : ℝ), (17341271162561/50000000000000 : ℝ), (1600120789731/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378529703/10000000000 : ℝ)|^8237 ≤ (33315041865607/100000000000000 : ℝ)^6189
        have hw : |(4378529703/10000000000 : ℝ)|=(4378529703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512893477/10000000000 : ℝ)|^8237 ≤ (17341271162561/50000000000000 : ℝ)^6189
        have hw : |(4512893477/10000000000 : ℝ)|=(4512893477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248261649/10000000000 : ℝ)|^8237 ≤ (1600120789731/5000000000000 : ℝ)^6189
        have hw : |(4248261649/10000000000 : ℝ)|=(4248261649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5581/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5487/50000 : ℝ) ^ (2059/512 : ℝ) ≤ (6915326164498141/50000000000000000000 : ℝ) := by
    have hpowers : (5487/50000 : ℝ)^2059 ≤ (6915326164498141/50000000000000000000 : ℝ)^512 := by
      have hnat : (5487 : ℕ)^2059*50000000000000000000^512 ≤ 6915326164498141^512*50000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5487 50000 6915326164498141 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5487/50000 : ℝ)) (X := (6915326164498141/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14247/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (3951044980358489/10000000000000000000 : ℝ) := by
    have hpowers : (14247/100000 : ℝ)^2059 ≤ (3951044980358489/10000000000000000000 : ℝ)^512 := by
      have hnat : (14247 : ℕ)^2059*10000000000000000000^512 ≤ 3951044980358489^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 100000 3951044980358489 10000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/100000 : ℝ)) (X := (3951044980358489/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006915326164498141/25000000000000000000 : ℝ) ≤ (10000687766708239/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25006915326164498141/25000000000000000000 : ℝ)^512 ≤ (10000687766708239/10000000000000000 : ℝ)^2059 := by
      have hnat : (25006915326164498141 : ℕ)^512*10000000000000000^2059 ≤ 10000687766708239^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006915326164498141 25000000000000000000 10000687766708239 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000687766708239/10000000000000000 : ℝ)) (X := (25006915326164498141/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013335275533145293/25000000000000000000 : ℝ) ≤ (100013261376077/100000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25013335275533145293/25000000000000000000 : ℝ)^512 ≤ (100013261376077/100000000000000 : ℝ)^2059 := by
      have hnat : (25013335275533145293 : ℕ)^512*100000000000000^2059 ≤ 100013261376077^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013335275533145293 25000000000000000000 100013261376077 100000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100013261376077/100000000000000 : ℝ)) (X := (25013335275533145293/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003951044980358489/5000000000000000000 : ℝ) ≤ (10001964508507161/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (5003951044980358489/5000000000000000000 : ℝ)^512 ≤ (10001964508507161/10000000000000000 : ℝ)^2059 := by
      have hnat : (5003951044980358489 : ℕ)^512*10000000000000000^2059 ≤ 10001964508507161^2059*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003951044980358489 5000000000000000000 10001964508507161 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001964508507161/10000000000000000 : ℝ)) (X := (5003951044980358489/5000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6915326164498141/50000000000000000000 : ℝ) ≤ ((10906080031978232073/10910000000000000000 : ℝ)+2*(638370899461/327300000000000 : ℝ)*(5487/50000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (10906080031978232073/10910000000000000000 : ℝ)+2*(638370899461/327300000000000 : ℝ)*(5487/50000 : ℝ)=(10000687766708239/10000000000000000 : ℝ) by norm_num, show 1+2*(6915326164498141/50000000000000000000 : ℝ)=(25006915326164498141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3951044980358489/10000000000000000000 : ℝ)+(6915326164498141/50000000000000000000 : ℝ) ≤ ((10906080031978232073/10910000000000000000 : ℝ)+(638370899461/327300000000000 : ℝ)*((14247/100000 : ℝ)+(5487/50000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (10906080031978232073/10910000000000000000 : ℝ)+(638370899461/327300000000000 : ℝ)*((14247/100000 : ℝ)+(5487/50000 : ℝ))=(100013261376077/100000000000000 : ℝ) by norm_num, show 1+(3951044980358489/10000000000000000000 : ℝ)+(6915326164498141/50000000000000000000 : ℝ)=(25013335275533145293/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3951044980358489/10000000000000000000 : ℝ) ≤ ((10906080031978232073/10910000000000000000 : ℝ)+2*(638370899461/327300000000000 : ℝ)*(14247/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (10906080031978232073/10910000000000000000 : ℝ)+2*(638370899461/327300000000000 : ℝ)*(14247/100000 : ℝ)=(10001964508507161/10000000000000000 : ℝ) by norm_num, show 1+2*(3951044980358489/10000000000000000000 : ℝ)=(5003951044980358489/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10906080031978232073/10910000000000000000 : ℝ)*(X 1 0+X 2 0)+(638370899461/327300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (10906080031978232073/10910000000000000000 : ℝ)) (alpha := (638370899461/327300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10906080031978232073/10910000000000000000 : ℝ)*(X 0 1+X 2 1)+(638370899461/327300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (10906080031978232073/10910000000000000000 : ℝ)) (alpha := (638370899461/327300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10906080031978232073/10910000000000000000 : ℝ)*(X 0 2+X 1 2)+(638370899461/327300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (10906080031978232073/10910000000000000000 : ℝ)) (alpha := (638370899461/327300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88575719/400000000 : ℝ)*X 0 0+(5397638921/10000000000 : ℝ)*X 0 1+(5261308059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336436653/2500000000 : ℝ)*X 1 0+(-2283612717/10000000000 : ℝ)*X 1 1+(2630654053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672873303/5000000000 : ℝ)*X 2 0+(5261308071/10000000000 : ℝ)*X 2 1+(-2283612771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547314847/1250000000 : ℝ)*X 0 0+(424756447/1000000000 : ℝ)*X 0 1+(902717527/2000000000 : ℝ)*X 0 2+(547314847/1250000000 : ℝ)*X 1 0+(424756447/1000000000 : ℝ)*X 1 1+(902717527/2000000000 : ℝ)*X 1 2+(547314847/1250000000 : ℝ)*X 2 0+(424756447/1000000000 : ℝ)*X 2 1+(902717527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221439853/1000000000 : ℝ)*X 0 0+(5261663887/10000000000 : ℝ)*X 0 1+(1349320487/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062293761/2000000000 : ℝ)*X 1 0+(-1677843/7812500 : ℝ)*X 1 1+(5397281707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327867177/2500000000 : ℝ)*X 2 0+(1349320431/2500000000 : ℝ)*X 2 1+(-536909787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378529703/10000000000 : ℝ)*X 0 0+(4512893477/10000000000 : ℝ)*X 0 1+(4248261649/10000000000 : ℝ)*X 0 2+(4378529703/10000000000 : ℝ)*X 1 0+(4512893477/10000000000 : ℝ)*X 1 1+(4248261649/10000000000 : ℝ)*X 1 2+(4378529703/10000000000 : ℝ)*X 2 0+(4512893477/10000000000 : ℝ)*X 2 1+(4248261649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29337244011621095026291/2727500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2093177929/100000000000000 : ℝ)*(base19) + (1911894599/100000000000000 : ℝ)*(base23) + (18501671/20000000000000 : ℝ)*(lower2) + (327732999/100000000000000 : ℝ)*(upper3) + (28747317/25000000000000 : ℝ)*(upper5) + (2773583815995031/50000000000000 : ℝ)*(major0) + (2773583815995031/50000000000000 : ℝ)*(major1) + (2773583815995031/50000000000000 : ℝ)*(major2) + (146703096431211/2000000000000 : ℝ)*(sp0) + (73352041084677/1000000000000 : ℝ)*(sp1) + (733520428975103/10000000000000 : ℝ)*(sp2) + (939774339981567/25000000000000 : ℝ)*(sp3) + (25690042539/50000000000000 : ℝ)*(sp4) + (1567193589/5000000000000 : ℝ)*(sp7) + (117472771993689/3125000000000 : ℝ)*(f.failure) + (7335206201645629/100000000000000 : ℝ)*(f.sum) + (605942974811/2045625000000000000000000000 : ℝ)*base66 + (10238555703666412211/1636500000000000000000000000000000 : ℝ)*base68 + (13742086818146587789/1636500000000000000000000000000000 : ℝ)*base69 + (34214262525114412211/1636500000000000000000000000000000 : ℝ)*base72 + (7008045276391/8182500000000000000000000000 : ℝ)*base73 + (3294455117627587789/1636500000000000000000000000000000 : ℝ)*base75 + (12555153506915587789/1636500000000000000000000000000000 : ℝ)*base77 + (53084119605447412211/1636500000000000000000000000000000 : ℝ)*base80 + (8120831883371/2045625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (36439/312500000000000000000 : ℝ)*base90 + (36439/312500000000000000000 : ℝ)*base92 + (36439/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (312564018137740871461857933/34093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90457041/10000000000000 : ℝ)*(base19) + (485220039/50000000000000 : ℝ)*(base23) + (113915183/100000000000000 : ℝ)*(lower4) + (550587/2000000000000 : ℝ)*(upper5) + (697030456406143/12500000000000 : ℝ)*(major0) + (697030456406143/12500000000000 : ℝ)*(major1) + (697030456406143/12500000000000 : ℝ)*(major2) + (1072344489/25000000000000 : ℝ)*(sp0) + (5460022057/25000000000000 : ℝ)*(sp1) + (19679957907/100000000000000 : ℝ)*(sp2) + (7373650164610203/100000000000000 : ℝ)*(sp4) + (7373631709329521/100000000000000 : ℝ)*(sp5) + (3686816901795087/50000000000000 : ℝ)*(sp6) + (1889416271458717/50000000000000 : ℝ)*(sp7) + (1889416271458717/50000000000000 : ℝ)*(f.failure) + (7373654453988159/100000000000000 : ℝ)*(f.sum) + (16134602251001/4091250000000000000000000000 : ℝ)*base65 + (1812051669768398317/409125000000000000000000000000000 : ℝ)*base67 + (1716680966917523317/409125000000000000000000000000000 : ℝ)*base69 + (8879818810740398317/409125000000000000000000000000000 : ℝ)*base71 + (36858202553423/8182500000000000000000000000 : ℝ)*base74 + (2191152431593851683/409125000000000000000000000000000 : ℝ)*base76 + (2351733210891773317/409125000000000000000000000000000 : ℝ)*base77 + (5079453679489898317/409125000000000000000000000000000 : ℝ)*base79 + (80503363224179/16365000000000000000000000000 : ℝ)*base81 + (32674467/5000000000000000000000 : ℝ)*base90 + (32674467/5000000000000000000000 : ℝ)*base92 + (32674467/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1044_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1044_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1044_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1044_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1044_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
