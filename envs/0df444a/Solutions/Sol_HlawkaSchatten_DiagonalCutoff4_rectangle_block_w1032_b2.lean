-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:40:15.278189+00:00
-- url     : https://prove2.me/submissions/a74e12e7-6647-47cc-9f9b-b2c646207e62

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
theorem support_rectangle_w1032_s6_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88822471/400000000 : ℝ)*x 0 + (5395612453/10000000000 : ℝ)*x 1 + (1315795523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88822471/400000000 : ℝ)^8225 ≤ (13482827086051/100000000000000 : ℝ)^6177 := by
    have hnat : (88822471 : ℕ)^8225*100000000000000^6177 ≤ 13482827086051^6177*400000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88822471 400000000 13482827086051 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395612453/10000000000 : ℝ)^8225 ≤ (1758968940667/4000000000000 : ℝ)^6177 := by
    have hnat : (5395612453 : ℕ)^8225*4000000000000^6177 ≤ 1758968940667^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395612453 10000000000 1758968940667 4000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315795523/2500000000 : ℝ)^8225 ≤ (21271474692969/50000000000000 : ℝ)^6177 := by
    have hnat : (1315795523 : ℕ)^8225*50000000000000^6177 ≤ 21271474692969^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315795523 2500000000 21271474692969 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88822471/400000000 : ℝ), (5395612453/10000000000 : ℝ), (1315795523/2500000000 : ℝ)] ![(13482827086051/100000000000000 : ℝ), (1758968940667/4000000000000 : ℝ), (21271474692969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88822471/400000000 : ℝ)|^8225 ≤ (13482827086051/100000000000000 : ℝ)^6177
        have hw : |(-88822471/400000000 : ℝ)|=(88822471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395612453/10000000000 : ℝ)|^8225 ≤ (1758968940667/4000000000000 : ℝ)^6177
        have hw : |(5395612453/10000000000 : ℝ)|=(5395612453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315795523/2500000000 : ℝ)|^8225 ≤ (21271474692969/50000000000000 : ℝ)^6177
        have hw : |(1315795523/2500000000 : ℝ)|=(1315795523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672606243/5000000000 : ℝ)*x 0 + (-2287772181/10000000000 : ℝ)*x 1 + (2631591011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672606243/5000000000 : ℝ)^8225 ≤ (43428124299483/100000000000000 : ℝ)^6177 := by
    have hnat : (2672606243 : ℕ)^8225*100000000000000^6177 ≤ 43428124299483^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672606243 5000000000 43428124299483 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287772181/10000000000 : ℝ)^8225 ≤ (2805785411883/20000000000000 : ℝ)^6177 := by
    have hnat : (2287772181 : ℕ)^8225*20000000000000^6177 ≤ 2805785411883^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287772181 10000000000 2805785411883 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631591011/5000000000 : ℝ)^8225 ≤ (42542948632521/100000000000000 : ℝ)^6177 := by
    have hnat : (2631591011 : ℕ)^8225*100000000000000^6177 ≤ 42542948632521^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631591011 5000000000 42542948632521 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672606243/5000000000 : ℝ), (-2287772181/10000000000 : ℝ), (2631591011/5000000000 : ℝ)] ![(43428124299483/100000000000000 : ℝ), (2805785411883/20000000000000 : ℝ), (42542948632521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672606243/5000000000 : ℝ)|^8225 ≤ (43428124299483/100000000000000 : ℝ)^6177
        have hw : |(2672606243/5000000000 : ℝ)|=(2672606243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2287772181/10000000000 : ℝ)|^8225 ≤ (2805785411883/20000000000000 : ℝ)^6177
        have hw : |(-2287772181/10000000000 : ℝ)|=(2287772181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631591011/5000000000 : ℝ)|^8225 ≤ (42542948632521/100000000000000 : ℝ)^6177
        have hw : |(2631591011/5000000000 : ℝ)|=(2631591011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345212561/10000000000 : ℝ)*x 0 + (5263181983/10000000000 : ℝ)*x 1 + (-2287772131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345212561/10000000000 : ℝ)^8225 ≤ (21714062555433/50000000000000 : ℝ)^6177 := by
    have hnat : (5345212561 : ℕ)^8225*50000000000000^6177 ≤ 21714062555433^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345212561 10000000000 21714062555433 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263181983/10000000000 : ℝ)^8225 ≤ (1063573705319/2500000000000 : ℝ)^6177 := by
    have hnat : (5263181983 : ℕ)^8225*2500000000000^6177 ≤ 1063573705319^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263181983 10000000000 1063573705319 2500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287772131/10000000000 : ℝ)^8225 ≤ (876807915697/6250000000000 : ℝ)^6177 := by
    have hnat : (2287772131 : ℕ)^8225*6250000000000^6177 ≤ 876807915697^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287772131 10000000000 876807915697 6250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345212561/10000000000 : ℝ), (5263181983/10000000000 : ℝ), (-2287772131/10000000000 : ℝ)] ![(21714062555433/50000000000000 : ℝ), (1063573705319/2500000000000 : ℝ), (876807915697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345212561/10000000000 : ℝ)|^8225 ≤ (21714062555433/50000000000000 : ℝ)^6177
        have hw : |(5345212561/10000000000 : ℝ)|=(5345212561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263181983/10000000000 : ℝ)|^8225 ≤ (1063573705319/2500000000000 : ℝ)^6177
        have hw : |(5263181983/10000000000 : ℝ)|=(5263181983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2287772131/10000000000 : ℝ)|^8225 ≤ (876807915697/6250000000000 : ℝ)^6177
        have hw : |(-2287772131/10000000000 : ℝ)|=(2287772131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4380371317/10000000000 : ℝ)*x 0 + (4253411481/10000000000 : ℝ)*x 1 + (2255602791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380371317/10000000000 : ℝ)^8225 ≤ (1332640345243/4000000000000 : ℝ)^6177 := by
    have hnat : (4380371317 : ℕ)^8225*4000000000000^6177 ≤ 1332640345243^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380371317 10000000000 1332640345243 4000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253411481/10000000000 : ℝ)^8225 ≤ (1001138964909/3125000000000 : ℝ)^6177 := by
    have hnat : (4253411481 : ℕ)^8225*3125000000000^6177 ≤ 1001138964909^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253411481 10000000000 1001138964909 3125000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255602791/5000000000 : ℝ)^8225 ≤ (17323772236617/50000000000000 : ℝ)^6177 := by
    have hnat : (2255602791 : ℕ)^8225*50000000000000^6177 ≤ 17323772236617^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255602791 5000000000 17323772236617 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380371317/10000000000 : ℝ), (4253411481/10000000000 : ℝ), (2255602791/5000000000 : ℝ)] ![(1332640345243/4000000000000 : ℝ), (1001138964909/3125000000000 : ℝ), (17323772236617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380371317/10000000000 : ℝ)|^8225 ≤ (1332640345243/4000000000000 : ℝ)^6177
        have hw : |(4380371317/10000000000 : ℝ)|=(4380371317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253411481/10000000000 : ℝ)|^8225 ≤ (1001138964909/3125000000000 : ℝ)^6177
        have hw : |(4253411481/10000000000 : ℝ)|=(4253411481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255602791/5000000000 : ℝ)|^8225 ≤ (17323772236617/50000000000000 : ℝ)^6177
        have hw : |(2255602791/5000000000 : ℝ)|=(2255602791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220567563/10000000000 : ℝ)*x 0 + (328969787/625000000 : ℝ)*x 1 + (2697638189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220567563/10000000000 : ℝ)^8225 ≤ (13482873881661/100000000000000 : ℝ)^6177 := by
    have hnat : (2220567563 : ℕ)^8225*100000000000000^6177 ≤ 13482873881661^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220567563 10000000000 13482873881661 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328969787/625000000 : ℝ)^8225 ≤ (42546549681891/100000000000000 : ℝ)^6177 := by
    have hnat : (328969787 : ℕ)^8225*100000000000000^6177 ≤ 42546549681891^6177*625000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328969787 625000000 42546549681891 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697638189/5000000000 : ℝ)^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177 := by
    have hnat : (2697638189 : ℕ)^8225*12500000000000^6177 ≤ 5496322052307^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697638189 5000000000 5496322052307 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220567563/10000000000 : ℝ), (328969787/625000000 : ℝ), (2697638189/5000000000 : ℝ)] ![(13482873881661/100000000000000 : ℝ), (42546549681891/100000000000000 : ℝ), (5496322052307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220567563/10000000000 : ℝ)|^8225 ≤ (13482873881661/100000000000000 : ℝ)^6177
        have hw : |(-2220567563/10000000000 : ℝ)|=(2220567563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328969787/625000000 : ℝ)|^8225 ≤ (42546549681891/100000000000000 : ℝ)^6177
        have hw : |(328969787/625000000 : ℝ)|=(328969787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697638189/5000000000 : ℝ)|^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177
        have hw : |(2697638189/5000000000 : ℝ)|=(2697638189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062389481/2000000000 : ℝ)*x 0 + (-2155677957/10000000000 : ℝ)*x 1 + (2697638189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062389481/2000000000 : ℝ)^8225 ≤ (5383577500921/12500000000000 : ℝ)^6177 := by
    have hnat : (1062389481 : ℕ)^8225*12500000000000^6177 ≤ 5383577500921^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062389481 2000000000 5383577500921 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155677957/10000000000 : ℝ)^8225 ≤ (12960803554447/100000000000000 : ℝ)^6177 := by
    have hnat : (2155677957 : ℕ)^8225*100000000000000^6177 ≤ 12960803554447^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155677957 10000000000 12960803554447 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697638189/5000000000 : ℝ)^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177 := by
    have hnat : (2697638189 : ℕ)^8225*12500000000000^6177 ≤ 5496322052307^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697638189 5000000000 5496322052307 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062389481/2000000000 : ℝ), (-2155677957/10000000000 : ℝ), (2697638189/5000000000 : ℝ)] ![(5383577500921/12500000000000 : ℝ), (12960803554447/100000000000000 : ℝ), (5496322052307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062389481/2000000000 : ℝ)|^8225 ≤ (5383577500921/12500000000000 : ℝ)^6177
        have hw : |(1062389481/2000000000 : ℝ)|=(1062389481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155677957/10000000000 : ℝ)|^8225 ≤ (12960803554447/100000000000000 : ℝ)^6177
        have hw : |(-2155677957/10000000000 : ℝ)|=(2155677957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697638189/5000000000 : ℝ)|^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177
        have hw : |(2697638189/5000000000 : ℝ)|=(2697638189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062389481/2000000000 : ℝ)*x 0 + (2697638189/5000000000 : ℝ)*x 1 + (-2155677957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062389481/2000000000 : ℝ)^8225 ≤ (5383577500921/12500000000000 : ℝ)^6177 := by
    have hnat : (1062389481 : ℕ)^8225*12500000000000^6177 ≤ 5383577500921^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062389481 2000000000 5383577500921 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697638189/5000000000 : ℝ)^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177 := by
    have hnat : (2697638189 : ℕ)^8225*12500000000000^6177 ≤ 5496322052307^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697638189 5000000000 5496322052307 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155677957/10000000000 : ℝ)^8225 ≤ (12960803554447/100000000000000 : ℝ)^6177 := by
    have hnat : (2155677957 : ℕ)^8225*100000000000000^6177 ≤ 12960803554447^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155677957 10000000000 12960803554447 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062389481/2000000000 : ℝ), (2697638189/5000000000 : ℝ), (-2155677957/10000000000 : ℝ)] ![(5383577500921/12500000000000 : ℝ), (5496322052307/12500000000000 : ℝ), (12960803554447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062389481/2000000000 : ℝ)|^8225 ≤ (5383577500921/12500000000000 : ℝ)^6177
        have hw : |(1062389481/2000000000 : ℝ)|=(1062389481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697638189/5000000000 : ℝ)|^8225 ≤ (5496322052307/12500000000000 : ℝ)^6177
        have hw : |(2697638189/5000000000 : ℝ)|=(2697638189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155677957/10000000000 : ℝ)|^8225 ≤ (12960803554447/100000000000000 : ℝ)^6177
        have hw : |(-2155677957/10000000000 : ℝ)|=(2155677957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s6_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (438038187/1000000000 : ℝ)*x 0 + (4510554131/10000000000 : ℝ)*x 1 + (2127032539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438038187/1000000000 : ℝ)^8225 ≤ (8329028876539/25000000000000 : ℝ)^6177 := by
    have hnat : (438038187 : ℕ)^8225*25000000000000^6177 ≤ 8329028876539^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438038187 1000000000 8329028876539 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510554131/10000000000 : ℝ)^8225 ≤ (1385635295937/4000000000000 : ℝ)^6177 := by
    have hnat : (4510554131 : ℕ)^8225*4000000000000^6177 ≤ 1385635295937^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510554131 10000000000 1385635295937 4000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127032539/5000000000 : ℝ)^8225 ≤ (32043002083359/100000000000000 : ℝ)^6177 := by
    have hnat : (2127032539 : ℕ)^8225*100000000000000^6177 ≤ 32043002083359^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127032539 5000000000 32043002083359 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(438038187/1000000000 : ℝ), (4510554131/10000000000 : ℝ), (2127032539/5000000000 : ℝ)] ![(8329028876539/25000000000000 : ℝ), (1385635295937/4000000000000 : ℝ), (32043002083359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(438038187/1000000000 : ℝ)|^8225 ≤ (8329028876539/25000000000000 : ℝ)^6177
        have hw : |(438038187/1000000000 : ℝ)|=(438038187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510554131/10000000000 : ℝ)|^8225 ≤ (1385635295937/4000000000000 : ℝ)^6177
        have hw : |(4510554131/10000000000 : ℝ)|=(4510554131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2127032539/5000000000 : ℝ)|^8225 ≤ (32043002083359/100000000000000 : ℝ)^6177
        have hw : |(2127032539/5000000000 : ℝ)|=(2127032539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1119/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11143/100000 : ℝ) ^ (257/64 : ℝ) ≤ (2979531121456371/20000000000000000000 : ℝ) := by
    have hpowers : (11143/100000 : ℝ)^257 ≤ (2979531121456371/20000000000000000000 : ℝ)^64 := by
      have hnat : (11143 : ℕ)^257*20000000000000000000^64 ≤ 2979531121456371^64*100000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11143 100000 2979531121456371 20000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11143/100000 : ℝ)) (X := (2979531121456371/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (257/64 : ℝ) ≤ (9434241952663399/25000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^257 ≤ (9434241952663399/25000000000000000000 : ℝ)^64 := by
      have hnat : (2809 : ℕ)^257*25000000000000000000^64 ≤ 9434241952663399^64*20000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 9434241952663399 25000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (9434241952663399/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002979531121456371/10000000000000000000 : ℝ) ≤ (5000370950703491/5000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (10002979531121456371/10000000000000000000 : ℝ)^64 ≤ (5000370950703491/5000000000000000 : ℝ)^257 := by
      have hnat : (10002979531121456371 : ℕ)^64*5000000000000000^257 ≤ 5000370950703491^257*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002979531121456371 10000000000000000000 5000370950703491 5000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000370950703491/5000000000000000 : ℝ)) (X := (10002979531121456371/10000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052634623417935451/100000000000000000000 : ℝ) ≤ (10001310486515159/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (100052634623417935451/100000000000000000000 : ℝ)^64 ≤ (10001310486515159/10000000000000000 : ℝ)^257 := by
      have hnat : (100052634623417935451 : ℕ)^64*10000000000000000^257 ≤ 10001310486515159^257*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052634623417935451 100000000000000000000 10001310486515159 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001310486515159/10000000000000000 : ℝ)) (X := (100052634623417935451/100000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509434241952663399/12500000000000000000 : ℝ) ≤ (1250234883952917/1250000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (12509434241952663399/12500000000000000000 : ℝ)^64 ≤ (1250234883952917/1250000000000000 : ℝ)^257 := by
      have hnat : (12509434241952663399 : ℕ)^64*1250000000000000^257 ≤ 1250234883952917^257*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509434241952663399 12500000000000000000 1250234883952917 1250000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250234883952917/1250000000000000 : ℝ)) (X := (12509434241952663399/12500000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2979531121456371/20000000000000000000 : ℝ) ≤ ((14504740755081114571/14510000000000000000 : ℝ)+2*(568585108177/290200000000000 : ℝ)*(11143/100000 : ℝ))^(257/64 : ℝ) := by
    rw [show (14504740755081114571/14510000000000000000 : ℝ)+2*(568585108177/290200000000000 : ℝ)*(11143/100000 : ℝ)=(5000370950703491/5000000000000000 : ℝ) by norm_num, show 1+2*(2979531121456371/20000000000000000000 : ℝ)=(10002979531121456371/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9434241952663399/25000000000000000000 : ℝ)+(2979531121456371/20000000000000000000 : ℝ) ≤ ((14504740755081114571/14510000000000000000 : ℝ)+(568585108177/290200000000000 : ℝ)*((2809/20000 : ℝ)+(11143/100000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (14504740755081114571/14510000000000000000 : ℝ)+(568585108177/290200000000000 : ℝ)*((2809/20000 : ℝ)+(11143/100000 : ℝ))=(10001310486515159/10000000000000000 : ℝ) by norm_num, show 1+(9434241952663399/25000000000000000000 : ℝ)+(2979531121456371/20000000000000000000 : ℝ)=(100052634623417935451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9434241952663399/25000000000000000000 : ℝ) ≤ ((14504740755081114571/14510000000000000000 : ℝ)+2*(568585108177/290200000000000 : ℝ)*(2809/20000 : ℝ))^(257/64 : ℝ) := by
    rw [show (14504740755081114571/14510000000000000000 : ℝ)+2*(568585108177/290200000000000 : ℝ)*(2809/20000 : ℝ)=(1250234883952917/1250000000000000 : ℝ) by norm_num, show 1+2*(9434241952663399/25000000000000000000 : ℝ)=(12509434241952663399/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14504740755081114571/14510000000000000000 : ℝ)*(X 1 0+X 2 0)+(568585108177/290200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (14504740755081114571/14510000000000000000 : ℝ)) (alpha := (568585108177/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14504740755081114571/14510000000000000000 : ℝ)*(X 0 1+X 2 1)+(568585108177/290200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (14504740755081114571/14510000000000000000 : ℝ)) (alpha := (568585108177/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14504740755081114571/14510000000000000000 : ℝ)*(X 0 2+X 1 2)+(568585108177/290200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (14504740755081114571/14510000000000000000 : ℝ)) (alpha := (568585108177/290200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88822471/400000000 : ℝ)*X 0 0+(5395612453/10000000000 : ℝ)*X 0 1+(1315795523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672606243/5000000000 : ℝ)*X 1 0+(-2287772181/10000000000 : ℝ)*X 1 1+(2631591011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345212561/10000000000 : ℝ)*X 2 0+(5263181983/10000000000 : ℝ)*X 2 1+(-2287772131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4380371317/10000000000 : ℝ)*X 0 0+(4253411481/10000000000 : ℝ)*X 0 1+(2255602791/5000000000 : ℝ)*X 0 2+(4380371317/10000000000 : ℝ)*X 1 0+(4253411481/10000000000 : ℝ)*X 1 1+(2255602791/5000000000 : ℝ)*X 1 2+(4380371317/10000000000 : ℝ)*X 2 0+(4253411481/10000000000 : ℝ)*X 2 1+(2255602791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2220567563/10000000000 : ℝ)*X 0 0+(328969787/625000000 : ℝ)*X 0 1+(2697638189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062389481/2000000000 : ℝ)*X 1 0+(-2155677957/10000000000 : ℝ)*X 1 1+(2697638189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062389481/2000000000 : ℝ)*X 2 0+(2697638189/5000000000 : ℝ)*X 2 1+(-2155677957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((438038187/1000000000 : ℝ)*X 0 0+(4510554131/10000000000 : ℝ)*X 0 1+(2127032539/5000000000 : ℝ)*X 0 2+(438038187/1000000000 : ℝ)*X 1 0+(4510554131/10000000000 : ℝ)*X 1 1+(2127032539/5000000000 : ℝ)*X 1 2+(438038187/1000000000 : ℝ)*X 2 0+(4510554131/10000000000 : ℝ)*X 2 1+(2127032539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38780363797049787487171713/3627500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (310177133/20000000000000 : ℝ)*(base19) + (1503817639/100000000000000 : ℝ)*(base23) + (219203001/100000000000000 : ℝ)*(lower2) + (68704931/50000000000000 : ℝ)*(lower4) + (4401113/25000000000000 : ℝ)*(lower5) + (28575877281333/500000000000 : ℝ)*(major0) + (28575877281333/500000000000 : ℝ)*(major1) + (28575877281333/500000000000 : ℝ)*(major2) + (7551187291603769/100000000000000 : ℝ)*(sp0) + (3775618676457797/50000000000000 : ℝ)*(sp1) + (377561869999181/5000000000000 : ℝ)*(sp2) + (3879087255255263/100000000000000 : ℝ)*(sp3) + (51612197489/100000000000000 : ℝ)*(sp4) + (24397121383/100000000000000 : ℝ)*(sp7) + (1939555826188323/50000000000000 : ℝ)*(f.failure) + (7551238903801259/100000000000000 : ℝ)*(f.sum) + (7310220573029/1451000000000000000000000000 : ℝ)*base66 + (84121937539798143/7255000000000000000000000000000 : ℝ)*base67 + (146387757324503143/7255000000000000000000000000000 : ℝ)*base69 + (140273506427078143/7255000000000000000000000000000 : ℝ)*base71 + (683773426621/725500000000000000000000000 : ℝ)*base74 + (105824098451613143/7255000000000000000000000000000 : ℝ)*base75 + (29523434720398143/7255000000000000000000000000000 : ℝ)*base77 + (142243588102973143/7255000000000000000000000000000 : ℝ)*base79 + (13883671081/14510000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11230287/5000000000000000000000 : ℝ)*base89 + (11230287/5000000000000000000000 : ℝ)*base91 + (11230287/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (523325248376970161492625489/181375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109443439/20000000000000 : ℝ)*(base19) + (595299507/100000000000000 : ℝ)*(base23) + (29297769/50000000000000 : ℝ)*(upper3) + (21814491/100000000000000 : ℝ)*(lower4) + (29576721/50000000000000 : ℝ)*(upper5) + (1436046294415047/25000000000000 : ℝ)*(major0) + (1436046294415047/25000000000000 : ℝ)*(major1) + (1436046294415047/25000000000000 : ℝ)*(major2) + (14639751511/100000000000000 : ℝ)*(sp1) + (1969997967/12500000000000 : ℝ)*(sp2) + (758956858164791/10000000000000 : ℝ)*(sp4) + (1897388348669801/25000000000000 : ℝ)*(sp5) + (7589552226364667/100000000000000 : ℝ)*(sp6) + (1949400838747533/50000000000000 : ℝ)*(sp7) + (1949400838747533/50000000000000 : ℝ)*(f.failure) + (758956858164791/10000000000000 : ℝ)*(f.sum) + (1393796953039/906875000000000000000000000 : ℝ)*base66 + (3182937660432799837/362750000000000000000000000000000 : ℝ)*base67 + (2308080875517299837/362750000000000000000000000000000 : ℝ)*base69 + (1874808554427799837/362750000000000000000000000000000 : ℝ)*base71 + (11901038628253/7255000000000000000000000000 : ℝ)*base73 + (3617624787151200163/362750000000000000000000000000000 : ℝ)*base76 + (3598808739599049837/362750000000000000000000000000000 : ℝ)*base77 + (3121672536615700163/362750000000000000000000000000000 : ℝ)*base80 + (6477908092323/7255000000000000000000000000 : ℝ)*base81 + (5535777/5000000000000000000000 : ℝ)*base89 + (5535777/5000000000000000000000 : ℝ)*base91 + (5535777/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1032_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s7_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220612593/10000000000 : ℝ)*x 0 + (2697534459/5000000000 : ℝ)*x 1 + (5263691933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220612593/10000000000 : ℝ)^8225 ≤ (13483237947721/100000000000000 : ℝ)^6177 := by
    have hnat : (2220612593 : ℕ)^8225*100000000000000^6177 ≤ 13483237947721^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220612593 10000000000 13483237947721 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697534459/5000000000 : ℝ)^8225 ≤ (43968325092531/100000000000000 : ℝ)^6177 := by
    have hnat : (2697534459 : ℕ)^8225*100000000000000^6177 ≤ 43968325092531^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697534459 5000000000 43968325092531 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263691933/10000000000 : ℝ)^8225 ≤ (21274218472679/50000000000000 : ℝ)^6177 := by
    have hnat : (5263691933 : ℕ)^8225*50000000000000^6177 ≤ 21274218472679^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263691933 10000000000 21274218472679 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220612593/10000000000 : ℝ), (2697534459/5000000000 : ℝ), (5263691933/10000000000 : ℝ)] ![(13483237947721/100000000000000 : ℝ), (43968325092531/100000000000000 : ℝ), (21274218472679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220612593/10000000000 : ℝ)|^8225 ≤ (13483237947721/100000000000000 : ℝ)^6177
        have hw : |(-2220612593/10000000000 : ℝ)|=(2220612593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697534459/5000000000 : ℝ)|^8225 ≤ (43968325092531/100000000000000 : ℝ)^6177
        have hw : |(2697534459/5000000000 : ℝ)|=(2697534459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263691933/10000000000 : ℝ)|^8225 ≤ (21274218472679/50000000000000 : ℝ)^6177
        have hw : |(5263691933/10000000000 : ℝ)|=(5263691933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345076347/10000000000 : ℝ)*x 0 + (-57182007/250000000 : ℝ)*x 1 + (5263692011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345076347/10000000000 : ℝ)^8225 ≤ (5428331436863/12500000000000 : ℝ)^6177 := by
    have hnat : (5345076347 : ℕ)^8225*12500000000000^6177 ≤ 5428331436863^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345076347 10000000000 5428331436863 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57182007/250000000 : ℝ)^8225 ≤ (3506227675827/25000000000000 : ℝ)^6177 := by
    have hnat : (57182007 : ℕ)^8225*25000000000000^6177 ≤ 3506227675827^6177*250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57182007 250000000 3506227675827 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263692011/10000000000 : ℝ)^8225 ≤ (10637109446227/25000000000000 : ℝ)^6177 := by
    have hnat : (5263692011 : ℕ)^8225*25000000000000^6177 ≤ 10637109446227^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263692011 10000000000 10637109446227 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345076347/10000000000 : ℝ), (-57182007/250000000 : ℝ), (5263692011/10000000000 : ℝ)] ![(5428331436863/12500000000000 : ℝ), (3506227675827/25000000000000 : ℝ), (10637109446227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345076347/10000000000 : ℝ)|^8225 ≤ (5428331436863/12500000000000 : ℝ)^6177
        have hw : |(5345076347/10000000000 : ℝ)|=(5345076347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57182007/250000000 : ℝ)|^8225 ≤ (3506227675827/25000000000000 : ℝ)^6177
        have hw : |(-57182007/250000000 : ℝ)|=(57182007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263692011/10000000000 : ℝ)|^8225 ≤ (10637109446227/25000000000000 : ℝ)^6177
        have hw : |(5263692011/10000000000 : ℝ)|=(5263692011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345076369/10000000000 : ℝ)*x 0 + (1315922987/2500000000 : ℝ)*x 1 + (-1143640167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345076369/10000000000 : ℝ)^8225 ≤ (10856662933227/25000000000000 : ℝ)^6177 := by
    have hnat : (5345076369 : ℕ)^8225*25000000000000^6177 ≤ 10856662933227^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345076369 10000000000 10856662933227 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315922987/2500000000 : ℝ)^8225 ≤ (4254843710681/10000000000000 : ℝ)^6177 := by
    have hnat : (1315922987 : ℕ)^8225*10000000000000^6177 ≤ 4254843710681^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315922987 2500000000 4254843710681 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143640167/5000000000 : ℝ)^8225 ≤ (14024911144201/100000000000000 : ℝ)^6177 := by
    have hnat : (1143640167 : ℕ)^8225*100000000000000^6177 ≤ 14024911144201^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143640167 5000000000 14024911144201 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345076369/10000000000 : ℝ), (1315922987/2500000000 : ℝ), (-1143640167/5000000000 : ℝ)] ![(10856662933227/25000000000000 : ℝ), (4254843710681/10000000000000 : ℝ), (14024911144201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345076369/10000000000 : ℝ)|^8225 ≤ (10856662933227/25000000000000 : ℝ)^6177
        have hw : |(5345076369/10000000000 : ℝ)|=(5345076369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315922987/2500000000 : ℝ)|^8225 ≤ (4254843710681/10000000000000 : ℝ)^6177
        have hw : |(1315922987/2500000000 : ℝ)|=(1315922987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143640167/5000000000 : ℝ)|^8225 ≤ (14024911144201/100000000000000 : ℝ)^6177
        have hw : |(-1143640167/5000000000 : ℝ)|=(1143640167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1095099663/2500000000 : ℝ)*x 0 + (4254432893/10000000000 : ℝ)*x 1 + (1127544189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095099663/2500000000 : ℝ)^8225 ≤ (16658142732679/50000000000000 : ℝ)^6177 := by
    have hnat : (1095099663 : ℕ)^8225*50000000000000^6177 ≤ 16658142732679^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095099663 2500000000 16658142732679 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254432893/10000000000 : ℝ)^8225 ≤ (32046691205507/100000000000000 : ℝ)^6177 := by
    have hnat : (4254432893 : ℕ)^8225*100000000000000^6177 ≤ 32046691205507^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254432893 10000000000 32046691205507 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127544189/2500000000 : ℝ)^8225 ≤ (6927404662489/20000000000000 : ℝ)^6177 := by
    have hnat : (1127544189 : ℕ)^8225*20000000000000^6177 ≤ 6927404662489^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127544189 2500000000 6927404662489 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095099663/2500000000 : ℝ), (4254432893/10000000000 : ℝ), (1127544189/2500000000 : ℝ)] ![(16658142732679/50000000000000 : ℝ), (32046691205507/100000000000000 : ℝ), (6927404662489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095099663/2500000000 : ℝ)|^8225 ≤ (16658142732679/50000000000000 : ℝ)^6177
        have hw : |(1095099663/2500000000 : ℝ)|=(1095099663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254432893/10000000000 : ℝ)|^8225 ≤ (32046691205507/100000000000000 : ℝ)^6177
        have hw : |(4254432893/10000000000 : ℝ)|=(4254432893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127544189/2500000000 : ℝ)|^8225 ≤ (6927404662489/20000000000000 : ℝ)^6177
        have hw : |(1127544189/2500000000 : ℝ)|=(1127544189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-555154453/2500000000 : ℝ)*x 0 + (2632010507/5000000000 : ℝ)*x 1 + (5394738621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (555154453/2500000000 : ℝ)^8225 ≤ (13483280143321/100000000000000 : ℝ)^6177 := by
    have hnat : (555154453 : ℕ)^8225*100000000000000^6177 ≤ 13483280143321^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555154453 2500000000 13483280143321 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632010507/5000000000 : ℝ)^8225 ≤ (10637994757147/25000000000000 : ℝ)^6177 := by
    have hnat : (2632010507 : ℕ)^8225*25000000000000^6177 ≤ 10637994757147^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632010507 5000000000 10637994757147 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394738621/10000000000 : ℝ)^8225 ≤ (10991185204117/25000000000000 : ℝ)^6177 := by
    have hnat : (5394738621 : ℕ)^8225*25000000000000^6177 ≤ 10991185204117^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394738621 10000000000 10991185204117 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-555154453/2500000000 : ℝ), (2632010507/5000000000 : ℝ), (5394738621/10000000000 : ℝ)] ![(13483280143321/100000000000000 : ℝ), (10637994757147/25000000000000 : ℝ), (10991185204117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-555154453/2500000000 : ℝ)|^8225 ≤ (13483280143321/100000000000000 : ℝ)^6177
        have hw : |(-555154453/2500000000 : ℝ)|=(555154453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632010507/5000000000 : ℝ)|^8225 ≤ (10637994757147/25000000000000 : ℝ)^6177
        have hw : |(2632010507/5000000000 : ℝ)|=(2632010507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394738621/10000000000 : ℝ)|^8225 ≤ (10991185204117/25000000000000 : ℝ)^6177
        have hw : |(5394738621/10000000000 : ℝ)|=(5394738621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328018963/2500000000 : ℝ)*x 0 + (-2156233661/10000000000 : ℝ)*x 1 + (1348684651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328018963/2500000000 : ℝ)^8225 ≤ (43070006735103/100000000000000 : ℝ)^6177 := by
    have hnat : (1328018963 : ℕ)^8225*100000000000000^6177 ≤ 43070006735103^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328018963 2500000000 43070006735103 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156233661/10000000000 : ℝ)^8225 ≤ (3241313154049/25000000000000 : ℝ)^6177 := by
    have hnat : (2156233661 : ℕ)^8225*25000000000000^6177 ≤ 3241313154049^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156233661 10000000000 3241313154049 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348684651/2500000000 : ℝ)^8225 ≤ (43964740631991/100000000000000 : ℝ)^6177 := by
    have hnat : (1348684651 : ℕ)^8225*100000000000000^6177 ≤ 43964740631991^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348684651 2500000000 43964740631991 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328018963/2500000000 : ℝ), (-2156233661/10000000000 : ℝ), (1348684651/2500000000 : ℝ)] ![(43070006735103/100000000000000 : ℝ), (3241313154049/25000000000000 : ℝ), (43964740631991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328018963/2500000000 : ℝ)|^8225 ≤ (43070006735103/100000000000000 : ℝ)^6177
        have hw : |(1328018963/2500000000 : ℝ)|=(1328018963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156233661/10000000000 : ℝ)|^8225 ≤ (3241313154049/25000000000000 : ℝ)^6177
        have hw : |(-2156233661/10000000000 : ℝ)|=(2156233661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348684651/2500000000 : ℝ)|^8225 ≤ (43964740631991/100000000000000 : ℝ)^6177
        have hw : |(1348684651/2500000000 : ℝ)|=(1348684651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312075849/10000000000 : ℝ)*x 0 + (5394738627/10000000000 : ℝ)*x 1 + (-2156233633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312075849/10000000000 : ℝ)^8225 ≤ (21535003351357/50000000000000 : ℝ)^6177 := by
    have hnat : (5312075849 : ℕ)^8225*50000000000000^6177 ≤ 21535003351357^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312075849 10000000000 21535003351357 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394738627/10000000000 : ℝ)^8225 ≤ (43964740881577/100000000000000 : ℝ)^6177 := by
    have hnat : (5394738627 : ℕ)^8225*100000000000000^6177 ≤ 43964740881577^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394738627 10000000000 43964740881577 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156233633/10000000000 : ℝ)^8225 ≤ (6482626196007/50000000000000 : ℝ)^6177 := by
    have hnat : (2156233633 : ℕ)^8225*50000000000000^6177 ≤ 6482626196007^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156233633 10000000000 6482626196007 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312075849/10000000000 : ℝ), (5394738627/10000000000 : ℝ), (-2156233633/10000000000 : ℝ)] ![(21535003351357/50000000000000 : ℝ), (43964740881577/100000000000000 : ℝ), (6482626196007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312075849/10000000000 : ℝ)|^8225 ≤ (21535003351357/50000000000000 : ℝ)^6177
        have hw : |(5312075849/10000000000 : ℝ)|=(5312075849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394738627/10000000000 : ℝ)|^8225 ≤ (43964740881577/100000000000000 : ℝ)^6177
        have hw : |(5394738627/10000000000 : ℝ)|=(5394738627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2156233633/10000000000 : ℝ)|^8225 ≤ (6482626196007/50000000000000 : ℝ)^6177
        have hw : |(-2156233633/10000000000 : ℝ)|=(2156233633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s7_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4380408649/10000000000 : ℝ)*x 0 + (4509536157/10000000000 : ℝ)*x 1 + (2127537943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380408649/10000000000 : ℝ)^8225 ≤ (33316386709779/100000000000000 : ℝ)^6177 := by
    have hnat : (4380408649 : ℕ)^8225*100000000000000^6177 ≤ 33316386709779^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380408649 10000000000 33316386709779 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509536157/10000000000 : ℝ)^8225 ≤ (17315236354307/50000000000000 : ℝ)^6177 := by
    have hnat : (4509536157 : ℕ)^8225*50000000000000^6177 ≤ 17315236354307^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509536157 10000000000 17315236354307 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127537943/5000000000 : ℝ)^8225 ≤ (4006642571299/12500000000000 : ℝ)^6177 := by
    have hnat : (2127537943 : ℕ)^8225*12500000000000^6177 ≤ 4006642571299^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127537943 5000000000 4006642571299 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380408649/10000000000 : ℝ), (4509536157/10000000000 : ℝ), (2127537943/5000000000 : ℝ)] ![(33316386709779/100000000000000 : ℝ), (17315236354307/50000000000000 : ℝ), (4006642571299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380408649/10000000000 : ℝ)|^8225 ≤ (33316386709779/100000000000000 : ℝ)^6177
        have hw : |(4380408649/10000000000 : ℝ)|=(4380408649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509536157/10000000000 : ℝ)|^8225 ≤ (17315236354307/50000000000000 : ℝ)^6177
        have hw : |(4509536157/10000000000 : ℝ)|=(4509536157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2127537943/5000000000 : ℝ)|^8225 ≤ (4006642571299/12500000000000 : ℝ)^6177
        have hw : |(2127537943/5000000000 : ℝ)|=(2127537943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (437/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1119/10000 : ℝ) ^ (257/64 : ℝ) ≤ (7575796855122533/50000000000000000000 : ℝ) := by
    have hpowers : (1119/10000 : ℝ)^257 ≤ (7575796855122533/50000000000000000000 : ℝ)^64 := by
      have hnat : (1119 : ℕ)^257*50000000000000000000^64 ≤ 7575796855122533^64*10000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1119 10000 7575796855122533 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1119/10000 : ℝ)) (X := (7575796855122533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2799/20000 : ℝ) ^ (257/64 : ℝ) ≤ (37200385277697941/100000000000000000000 : ℝ) := by
    have hpowers : (2799/20000 : ℝ)^257 ≤ (37200385277697941/100000000000000000000 : ℝ)^64 := by
      have hnat : (2799 : ℕ)^257*100000000000000000000^64 ≤ 37200385277697941^64*20000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 20000 37200385277697941 100000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/20000 : ℝ)) (X := (37200385277697941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007575796855122533/25000000000000000000 : ℝ) ≤ (2500188636513631/2500000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (25007575796855122533/25000000000000000000 : ℝ)^64 ≤ (2500188636513631/2500000000000000 : ℝ)^257 := by
      have hnat : (25007575796855122533 : ℕ)^64*2500000000000000^257 ≤ 2500188636513631^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007575796855122533 25000000000000000000 2500188636513631 2500000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188636513631/2500000000000000 : ℝ)) (X := (25007575796855122533/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052351978987943007/100000000000000000000 : ℝ) ≤ (1250162931334053/1250000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (100052351978987943007/100000000000000000000 : ℝ)^64 ≤ (1250162931334053/1250000000000000 : ℝ)^257 := by
      have hnat : (100052351978987943007 : ℕ)^64*1250000000000000^257 ≤ 1250162931334053^257*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052351978987943007 100000000000000000000 1250162931334053 1250000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250162931334053/1250000000000000 : ℝ)) (X := (100052351978987943007/100000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037200385277697941/50000000000000000000 : ℝ) ≤ (2500463088822581/2500000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50037200385277697941/50000000000000000000 : ℝ)^64 ≤ (2500463088822581/2500000000000000 : ℝ)^257 := by
      have hnat : (50037200385277697941 : ℕ)^64*2500000000000000^257 ≤ 2500463088822581^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037200385277697941 50000000000000000000 2500463088822581 2500000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500463088822581/2500000000000000 : ℝ)) (X := (50037200385277697941/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7575796855122533/50000000000000000000 : ℝ) ≤ ((467330533605572297/467500000000000000 : ℝ)+2*(5489046179/2805000000000 : ℝ)*(1119/10000 : ℝ))^(257/64 : ℝ) := by
    rw [show (467330533605572297/467500000000000000 : ℝ)+2*(5489046179/2805000000000 : ℝ)*(1119/10000 : ℝ)=(2500188636513631/2500000000000000 : ℝ) by norm_num, show 1+2*(7575796855122533/50000000000000000000 : ℝ)=(25007575796855122533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37200385277697941/100000000000000000000 : ℝ)+(7575796855122533/50000000000000000000 : ℝ) ≤ ((467330533605572297/467500000000000000 : ℝ)+(5489046179/2805000000000 : ℝ)*((2799/20000 : ℝ)+(1119/10000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (467330533605572297/467500000000000000 : ℝ)+(5489046179/2805000000000 : ℝ)*((2799/20000 : ℝ)+(1119/10000 : ℝ))=(1250162931334053/1250000000000000 : ℝ) by norm_num, show 1+(37200385277697941/100000000000000000000 : ℝ)+(7575796855122533/50000000000000000000 : ℝ)=(100052351978987943007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37200385277697941/100000000000000000000 : ℝ) ≤ ((467330533605572297/467500000000000000 : ℝ)+2*(5489046179/2805000000000 : ℝ)*(2799/20000 : ℝ))^(257/64 : ℝ) := by
    rw [show (467330533605572297/467500000000000000 : ℝ)+2*(5489046179/2805000000000 : ℝ)*(2799/20000 : ℝ)=(2500463088822581/2500000000000000 : ℝ) by norm_num, show 1+2*(37200385277697941/100000000000000000000 : ℝ)=(50037200385277697941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (467330533605572297/467500000000000000 : ℝ)*(X 1 0+X 2 0)+(5489046179/2805000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (467330533605572297/467500000000000000 : ℝ)) (alpha := (5489046179/2805000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (467330533605572297/467500000000000000 : ℝ)*(X 0 1+X 2 1)+(5489046179/2805000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (467330533605572297/467500000000000000 : ℝ)) (alpha := (5489046179/2805000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (467330533605572297/467500000000000000 : ℝ)*(X 0 2+X 1 2)+(5489046179/2805000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (467330533605572297/467500000000000000 : ℝ)) (alpha := (5489046179/2805000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2220612593/10000000000 : ℝ)*X 0 0+(2697534459/5000000000 : ℝ)*X 0 1+(5263691933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345076347/10000000000 : ℝ)*X 1 0+(-57182007/250000000 : ℝ)*X 1 1+(5263692011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345076369/10000000000 : ℝ)*X 2 0+(1315922987/2500000000 : ℝ)*X 2 1+(-1143640167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1095099663/2500000000 : ℝ)*X 0 0+(4254432893/10000000000 : ℝ)*X 0 1+(1127544189/2500000000 : ℝ)*X 0 2+(1095099663/2500000000 : ℝ)*X 1 0+(4254432893/10000000000 : ℝ)*X 1 1+(1127544189/2500000000 : ℝ)*X 1 2+(1095099663/2500000000 : ℝ)*X 2 0+(4254432893/10000000000 : ℝ)*X 2 1+(1127544189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-555154453/2500000000 : ℝ)*X 0 0+(2632010507/5000000000 : ℝ)*X 0 1+(5394738621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328018963/2500000000 : ℝ)*X 1 0+(-2156233661/10000000000 : ℝ)*X 1 1+(1348684651/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312075849/10000000000 : ℝ)*X 2 0+(5394738627/10000000000 : ℝ)*X 2 1+(-2156233633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4380408649/10000000000 : ℝ)*X 0 0+(4509536157/10000000000 : ℝ)*X 0 1+(2127537943/5000000000 : ℝ)*X 0 2+(4380408649/10000000000 : ℝ)*X 1 0+(4509536157/10000000000 : ℝ)*X 1 1+(2127537943/5000000000 : ℝ)*X 1 2+(4380408649/10000000000 : ℝ)*X 2 0+(4509536157/10000000000 : ℝ)*X 2 1+(2127537943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11560105420671793009/1375000000000000000000000 : ℝ) := by norm_num
    linear_combination (824341523/50000000000000 : ℝ)*(base19) + (1507239099/100000000000000 : ℝ)*(base23) + (11543597/12500000000000 : ℝ)*(lower2) + (272282591/100000000000000 : ℝ)*(upper3) + (16309603/25000000000000 : ℝ)*(upper5) + (576099362951033/10000000000000 : ℝ)*(major0) + (576099362951033/10000000000000 : ℝ)*(major1) + (576099362951033/10000000000000 : ℝ)*(major2) + (1902933352974349/25000000000000 : ℝ)*(sp0) + (7611775103213691/100000000000000 : ℝ)*(sp1) + (3805887622328819/50000000000000 : ℝ)*(sp2) + (977545890540847/25000000000000 : ℝ)*(sp3) + (21669999671/50000000000000 : ℝ)*(sp4) + (6666178887/25000000000000 : ℝ)*(sp7) + (488776278359867/12500000000000 : ℝ)*(f.failure) + (7611776751896737/100000000000000 : ℝ)*(f.sum) + (3259002041/4125000000000000000000000 : ℝ)*base66 + (6679547822682259/825000000000000000000000000000 : ℝ)*base67 + (7775093920067741/825000000000000000000000000000 : ℝ)*base70 + (8353266871742741/825000000000000000000000000000 : ℝ)*base72 + (515953387/825000000000000000000000 : ℝ)*base74 + (7246812360357259/825000000000000000000000000000 : ℝ)*base75 + (861020828867741/825000000000000000000000000000 : ℝ)*base78 + (11993877303582259/825000000000000000000000000000 : ℝ)*base79 + (18828853157/8250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6674823/1250000000000000000000 : ℝ)*base89 + (6674823/1250000000000000000000 : ℝ)*base91 + (6674823/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75663438716666955599005479/11687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78963497/6250000000000 : ℝ)*(base19) + (324628943/25000000000000 : ℝ)*(base23) + (30700949/25000000000000 : ℝ)*(upper3) + (1431569/10000000000000 : ℝ)*(lower4) + (16590647/12500000000000 : ℝ)*(upper5) + (5789982764497431/100000000000000 : ℝ)*(major0) + (5789982764497431/100000000000000 : ℝ)*(major1) + (5789982764497431/100000000000000 : ℝ)*(major2) + (136143071/400000000000 : ℝ)*(sp1) + (36043172261/100000000000000 : ℝ)*(sp2) + (3825039516997793/50000000000000 : ℝ)*(sp4) + (1912510933702971/25000000000000 : ℝ)*(sp5) + (239063802884611/3125000000000 : ℝ)*(sp6) + (1964943139601681/50000000000000 : ℝ)*(sp7) + (1964943139601681/50000000000000 : ℝ)*(f.failure) + (3825039516997793/50000000000000 : ℝ)*(f.sum) + (44504590171/18700000000000000000000000 : ℝ)*base65 + (15570718743730993/46750000000000000000000000000000 : ℝ)*base68 + (391535218956269007/46750000000000000000000000000000 : ℝ)*base69 + (62786567389769007/46750000000000000000000000000000 : ℝ)*base71 + (71315983919/93500000000000000000000000 : ℝ)*base74 + (228775641866269007/46750000000000000000000000000000 : ℝ)*base75 + (116199492441519007/46750000000000000000000000000000 : ℝ)*base77 + (683172484172269007/46750000000000000000000000000000 : ℝ)*base79 + (555315907989/93500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (52392011/5000000000000000000000 : ℝ)*base90 + (52392011/5000000000000000000000 : ℝ)*base92 + (52392011/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1032_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (437/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s8_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110310709/5000000000 : ℝ)*x 0 + (1348737223/2500000000 : ℝ)*x 1 + (2631903157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110310709/5000000000 : ℝ)^8225 ≤ (168541366223/1250000000000 : ℝ)^6177 := by
    have hnat : (1110310709 : ℕ)^8225*1250000000000^6177 ≤ 168541366223^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110310709 5000000000 168541366223 1250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348737223/2500000000 : ℝ)^8225 ≤ (43967022600839/100000000000000 : ℝ)^6177 := by
    have hnat : (1348737223 : ℕ)^8225*100000000000000^6177 ≤ 43967022600839^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348737223 2500000000 43967022600839 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631903157/5000000000 : ℝ)^8225 ≤ (42549668083839/100000000000000 : ℝ)^6177 := by
    have hnat : (2631903157 : ℕ)^8225*100000000000000^6177 ≤ 42549668083839^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631903157 5000000000 42549668083839 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110310709/5000000000 : ℝ), (1348737223/2500000000 : ℝ), (2631903157/5000000000 : ℝ)] ![(168541366223/1250000000000 : ℝ), (43967022600839/100000000000000 : ℝ), (42549668083839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110310709/5000000000 : ℝ)|^8225 ≤ (168541366223/1250000000000 : ℝ)^6177
        have hw : |(-1110310709/5000000000 : ℝ)|=(1110310709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348737223/2500000000 : ℝ)|^8225 ≤ (43967022600839/100000000000000 : ℝ)^6177
        have hw : |(1348737223/2500000000 : ℝ)|=(1348737223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631903157/5000000000 : ℝ)|^8225 ≤ (42549668083839/100000000000000 : ℝ)^6177
        have hw : |(2631903157/5000000000 : ℝ)|=(2631903157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345046901/10000000000 : ℝ)*x 0 + (-571792107/2500000000 : ℝ)*x 1 + (1315951613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345046901/10000000000 : ℝ)^8225 ≤ (1737053317531/4000000000000 : ℝ)^6177 := by
    have hnat : (5345046901 : ℕ)^8225*4000000000000^6177 ≤ 1737053317531^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345046901 10000000000 1737053317531 4000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571792107/2500000000 : ℝ)^8225 ≤ (7011998737613/50000000000000 : ℝ)^6177 := by
    have hnat : (571792107 : ℕ)^8225*50000000000000^6177 ≤ 7011998737613^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571792107 2500000000 7011998737613 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315951613/2500000000 : ℝ)^8225 ≤ (21274834784603/50000000000000 : ℝ)^6177 := by
    have hnat : (1315951613 : ℕ)^8225*50000000000000^6177 ≤ 21274834784603^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315951613 2500000000 21274834784603 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345046901/10000000000 : ℝ), (-571792107/2500000000 : ℝ), (1315951613/2500000000 : ℝ)] ![(1737053317531/4000000000000 : ℝ), (7011998737613/50000000000000 : ℝ), (21274834784603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345046901/10000000000 : ℝ)|^8225 ≤ (1737053317531/4000000000000 : ℝ)^6177
        have hw : |(5345046901/10000000000 : ℝ)|=(5345046901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571792107/2500000000 : ℝ)|^8225 ≤ (7011998737613/50000000000000 : ℝ)^6177
        have hw : |(-571792107/2500000000 : ℝ)|=(571792107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315951613/2500000000 : ℝ)|^8225 ≤ (21274834784603/50000000000000 : ℝ)^6177
        have hw : |(1315951613/2500000000 : ℝ)|=(1315951613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672523451/5000000000 : ℝ)*x 0 + (2631903187/5000000000 : ℝ)*x 1 + (-228716853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672523451/5000000000 : ℝ)^8225 ≤ (43426332949093/100000000000000 : ℝ)^6177 := by
    have hnat : (2672523451 : ℕ)^8225*100000000000000^6177 ≤ 43426332949093^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672523451 5000000000 43426332949093 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631903187/5000000000 : ℝ)^8225 ≤ (42549668729651/100000000000000 : ℝ)^6177 := by
    have hnat : (2631903187 : ℕ)^8225*100000000000000^6177 ≤ 42549668729651^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631903187 5000000000 42549668729651 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228716853/1000000000 : ℝ)^8225 ≤ (1402399830801/10000000000000 : ℝ)^6177 := by
    have hnat : (228716853 : ℕ)^8225*10000000000000^6177 ≤ 1402399830801^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228716853 1000000000 1402399830801 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672523451/5000000000 : ℝ), (2631903187/5000000000 : ℝ), (-228716853/1000000000 : ℝ)] ![(43426332949093/100000000000000 : ℝ), (42549668729651/100000000000000 : ℝ), (1402399830801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672523451/5000000000 : ℝ)|^8225 ≤ (43426332949093/100000000000000 : ℝ)^6177
        have hw : |(2672523451/5000000000 : ℝ)|=(2672523451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631903187/5000000000 : ℝ)|^8225 ≤ (42549668729651/100000000000000 : ℝ)^6177
        have hw : |(2631903187/5000000000 : ℝ)|=(2631903187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228716853/1000000000 : ℝ)|^8225 ≤ (1402399830801/10000000000000 : ℝ)^6177
        have hw : |(-228716853/1000000000 : ℝ)|=(228716853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (219020231/500000000 : ℝ)*x 0 + (1063665083/2500000000 : ℝ)*x 1 + (4509947763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219020231/500000000 : ℝ)^8225 ≤ (33316345906151/100000000000000 : ℝ)^6177 := by
    have hnat : (219020231 : ℕ)^8225*100000000000000^6177 ≤ 33316345906151^6177*500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219020231 500000000 33316345906151 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063665083/2500000000 : ℝ)^8225 ≤ (32048972433063/100000000000000 : ℝ)^6177 := by
    have hnat : (1063665083 : ℕ)^8225*100000000000000^6177 ≤ 32048972433063^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063665083 2500000000 32048972433063 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509947763/10000000000 : ℝ)^8225 ≤ (6926936330469/20000000000000 : ℝ)^6177 := by
    have hnat : (4509947763 : ℕ)^8225*20000000000000^6177 ≤ 6926936330469^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509947763 10000000000 6926936330469 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219020231/500000000 : ℝ), (1063665083/2500000000 : ℝ), (4509947763/10000000000 : ℝ)] ![(33316345906151/100000000000000 : ℝ), (32048972433063/100000000000000 : ℝ), (6926936330469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219020231/500000000 : ℝ)|^8225 ≤ (33316345906151/100000000000000 : ℝ)^6177
        have hw : |(219020231/500000000 : ℝ)|=(219020231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063665083/2500000000 : ℝ)|^8225 ≤ (32048972433063/100000000000000 : ℝ)^6177
        have hw : |(1063665083/2500000000 : ℝ)|=(1063665083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509947763/10000000000 : ℝ)|^8225 ≤ (6926936330469/20000000000000 : ℝ)^6177
        have hw : |(4509947763/10000000000 : ℝ)|=(4509947763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110313287/5000000000 : ℝ)*x 0 + (5264134411/10000000000 : ℝ)*x 1 + (5394619613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110313287/5000000000 : ℝ)^8225 ≤ (13483350984141/100000000000000 : ℝ)^6177 := by
    have hnat : (1110313287 : ℕ)^8225*100000000000000^6177 ≤ 13483350984141^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110313287 5000000000 13483350984141 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264134411/10000000000 : ℝ)^8225 ≤ (21276599800529/50000000000000 : ℝ)^6177 := by
    have hnat : (5264134411 : ℕ)^8225*50000000000000^6177 ≤ 21276599800529^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264134411 10000000000 21276599800529 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394619613/10000000000 : ℝ)^8225 ≤ (10990862349507/25000000000000 : ℝ)^6177 := by
    have hnat : (5394619613 : ℕ)^8225*25000000000000^6177 ≤ 10990862349507^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394619613 10000000000 10990862349507 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110313287/5000000000 : ℝ), (5264134411/10000000000 : ℝ), (5394619613/10000000000 : ℝ)] ![(13483350984141/100000000000000 : ℝ), (21276599800529/50000000000000 : ℝ), (10990862349507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110313287/5000000000 : ℝ)|^8225 ≤ (13483350984141/100000000000000 : ℝ)^6177
        have hw : |(-1110313287/5000000000 : ℝ)|=(1110313287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264134411/10000000000 : ℝ)|^8225 ≤ (21276599800529/50000000000000 : ℝ)^6177
        have hw : |(5264134411/10000000000 : ℝ)|=(5264134411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394619613/10000000000 : ℝ)|^8225 ≤ (10990862349507/25000000000000 : ℝ)^6177
        have hw : |(5394619613/10000000000 : ℝ)|=(5394619613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312105411/10000000000 : ℝ)*x 0 + (-1078177561/5000000000 : ℝ)*x 1 + (2697309789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312105411/10000000000 : ℝ)^8225 ≤ (8614065171769/20000000000000 : ℝ)^6177 := by
    have hnat : (5312105411 : ℕ)^8225*20000000000000^6177 ≤ 8614065171769^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312105411 10000000000 8614065171769 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078177561/5000000000 : ℝ)^8225 ≤ (12966225104473/100000000000000 : ℝ)^6177 := by
    have hnat : (1078177561 : ℕ)^8225*100000000000000^6177 ≤ 12966225104473^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078177561 5000000000 12966225104473 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697309789/5000000000 : ℝ)^8225 ≤ (21981724509113/50000000000000 : ℝ)^6177 := by
    have hnat : (2697309789 : ℕ)^8225*50000000000000^6177 ≤ 21981724509113^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697309789 5000000000 21981724509113 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312105411/10000000000 : ℝ), (-1078177561/5000000000 : ℝ), (2697309789/5000000000 : ℝ)] ![(8614065171769/20000000000000 : ℝ), (12966225104473/100000000000000 : ℝ), (21981724509113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312105411/10000000000 : ℝ)|^8225 ≤ (8614065171769/20000000000000 : ℝ)^6177
        have hw : |(5312105411/10000000000 : ℝ)|=(5312105411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078177561/5000000000 : ℝ)|^8225 ≤ (12966225104473/100000000000000 : ℝ)^6177
        have hw : |(-1078177561/5000000000 : ℝ)|=(1078177561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697309789/5000000000 : ℝ)|^8225 ≤ (21981724509113/50000000000000 : ℝ)^6177
        have hw : |(2697309789/5000000000 : ℝ)|=(2697309789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656052631/5000000000 : ℝ)*x 0 + (107892391/200000000 : ℝ)*x 1 + (-1078177681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656052631/5000000000 : ℝ)^8225 ≤ (8614064850043/20000000000000 : ℝ)^6177 := by
    have hnat : (2656052631 : ℕ)^8225*20000000000000^6177 ≤ 8614064850043^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656052631 5000000000 8614064850043 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107892391/200000000 : ℝ)^8225 ≤ (2747715544649/6250000000000 : ℝ)^6177 := by
    have hnat : (107892391 : ℕ)^8225*6250000000000^6177 ≤ 2747715544649^6177*200000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107892391 200000000 2747715544649 6250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078177681/5000000000 : ℝ)^8225 ≤ (1620778378259/12500000000000 : ℝ)^6177 := by
    have hnat : (1078177681 : ℕ)^8225*12500000000000^6177 ≤ 1620778378259^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078177681 5000000000 1620778378259 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656052631/5000000000 : ℝ), (107892391/200000000 : ℝ), (-1078177681/5000000000 : ℝ)] ![(8614064850043/20000000000000 : ℝ), (2747715544649/6250000000000 : ℝ), (1620778378259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656052631/5000000000 : ℝ)|^8225 ≤ (8614064850043/20000000000000 : ℝ)^6177
        have hw : |(2656052631/5000000000 : ℝ)|=(2656052631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107892391/200000000 : ℝ)|^8225 ≤ (2747715544649/6250000000000 : ℝ)^6177
        have hw : |(107892391/200000000 : ℝ)|=(107892391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078177681/5000000000 : ℝ)|^8225 ≤ (1620778378259/12500000000000 : ℝ)^6177
        have hw : |(-1078177681/5000000000 : ℝ)|=(1078177681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s8_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1095103593/2500000000 : ℝ)*x 0 + (2254654591/5000000000 : ℝ)*x 1 + (4255301491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095103593/2500000000 : ℝ)^8225 ≤ (33316444669383/100000000000000 : ℝ)^6177 := by
    have hnat : (1095103593 : ℕ)^8225*100000000000000^6177 ≤ 33316444669383^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095103593 2500000000 33316444669383 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254654591/5000000000 : ℝ)^8225 ≤ (17314075896761/50000000000000 : ℝ)^6177 := by
    have hnat : (2254654591 : ℕ)^8225*50000000000000^6177 ≤ 17314075896761^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254654591 5000000000 17314075896761 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255301491/10000000000 : ℝ)^8225 ≤ (32055403516031/100000000000000 : ℝ)^6177 := by
    have hnat : (4255301491 : ℕ)^8225*100000000000000^6177 ≤ 32055403516031^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255301491 10000000000 32055403516031 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095103593/2500000000 : ℝ), (2254654591/5000000000 : ℝ), (4255301491/10000000000 : ℝ)] ![(33316444669383/100000000000000 : ℝ), (17314075896761/50000000000000 : ℝ), (32055403516031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095103593/2500000000 : ℝ)|^8225 ≤ (33316444669383/100000000000000 : ℝ)^6177
        have hw : |(1095103593/2500000000 : ℝ)|=(1095103593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254654591/5000000000 : ℝ)|^8225 ≤ (17314075896761/50000000000000 : ℝ)^6177
        have hw : |(2254654591/5000000000 : ℝ)|=(2254654591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255301491/10000000000 : ℝ)|^8225 ≤ (32055403516031/100000000000000 : ℝ)^6177
        have hw : |(4255301491/10000000000 : ℝ)|=(4255301491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2801/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13981/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (437/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11201/100000 : ℝ) ^ (257/64 : ℝ) ≤ (15211492455936749/100000000000000000000 : ℝ) := by
    have hpowers : (11201/100000 : ℝ)^257 ≤ (15211492455936749/100000000000000000000 : ℝ)^64 := by
      have hnat : (11201 : ℕ)^257*100000000000000000000^64 ≤ 15211492455936749^64*100000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11201 100000 15211492455936749 100000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11201/100000 : ℝ)) (X := (15211492455936749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (437/3125 : ℝ) ^ (257/64 : ℝ) ≤ (18541555112117843/50000000000000000000 : ℝ) := by
    have hpowers : (437/3125 : ℝ)^257 ≤ (18541555112117843/50000000000000000000 : ℝ)^64 := by
      have hnat : (437 : ℕ)^257*50000000000000000000^64 ≤ 18541555112117843^64*3125^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        437 3125 18541555112117843 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (437/3125 : ℝ)) (X := (18541555112117843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015211492455936749/50000000000000000000 : ℝ) ≤ (10000757528658293/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50015211492455936749/50000000000000000000 : ℝ)^64 ≤ (10000757528658293/10000000000000000 : ℝ)^257 := by
      have hnat : (50015211492455936749 : ℕ)^64*10000000000000000^257 ≤ 10000757528658293^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015211492455936749 50000000000000000000 10000757528658293 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757528658293/10000000000000000 : ℝ)) (X := (50015211492455936749/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010458920536034487/20000000000000000000 : ℝ) ≤ (500065101120363/500000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (20010458920536034487/20000000000000000000 : ℝ)^64 ≤ (500065101120363/500000000000000 : ℝ)^257 := by
      have hnat : (20010458920536034487 : ℕ)^64*500000000000000^257 ≤ 500065101120363^257*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010458920536034487 20000000000000000000 500065101120363 500000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500065101120363/500000000000000 : ℝ)) (X := (20010458920536034487/20000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018541555112117843/25000000000000000000 : ℝ) ≤ (10001846516156227/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (25018541555112117843/25000000000000000000 : ℝ)^64 ≤ (10001846516156227/10000000000000000 : ℝ)^257 := by
      have hnat : (25018541555112117843 : ℕ)^64*10000000000000000^257 ≤ 10001846516156227^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018541555112117843 25000000000000000000 10001846516156227 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001846516156227/10000000000000000 : ℝ)) (X := (25018541555112117843/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15211492455936749/100000000000000000000 : ℝ) ≤ ((241912264811231919/242000000000000000 : ℝ)+2*(544493748967/278300000000000 : ℝ)*(11201/100000 : ℝ))^(257/64 : ℝ) := by
    rw [show (241912264811231919/242000000000000000 : ℝ)+2*(544493748967/278300000000000 : ℝ)*(11201/100000 : ℝ)=(10000757528658293/10000000000000000 : ℝ) by norm_num, show 1+2*(15211492455936749/100000000000000000000 : ℝ)=(50015211492455936749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18541555112117843/50000000000000000000 : ℝ)+(15211492455936749/100000000000000000000 : ℝ) ≤ ((241912264811231919/242000000000000000 : ℝ)+(544493748967/278300000000000 : ℝ)*((437/3125 : ℝ)+(11201/100000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (241912264811231919/242000000000000000 : ℝ)+(544493748967/278300000000000 : ℝ)*((437/3125 : ℝ)+(11201/100000 : ℝ))=(500065101120363/500000000000000 : ℝ) by norm_num, show 1+(18541555112117843/50000000000000000000 : ℝ)+(15211492455936749/100000000000000000000 : ℝ)=(20010458920536034487/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18541555112117843/50000000000000000000 : ℝ) ≤ ((241912264811231919/242000000000000000 : ℝ)+2*(544493748967/278300000000000 : ℝ)*(437/3125 : ℝ))^(257/64 : ℝ) := by
    rw [show (241912264811231919/242000000000000000 : ℝ)+2*(544493748967/278300000000000 : ℝ)*(437/3125 : ℝ)=(10001846516156227/10000000000000000 : ℝ) by norm_num, show 1+2*(18541555112117843/50000000000000000000 : ℝ)=(25018541555112117843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (241912264811231919/242000000000000000 : ℝ)*(X 1 0+X 2 0)+(544493748967/278300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (241912264811231919/242000000000000000 : ℝ)) (alpha := (544493748967/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (241912264811231919/242000000000000000 : ℝ)*(X 0 1+X 2 1)+(544493748967/278300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (241912264811231919/242000000000000000 : ℝ)) (alpha := (544493748967/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (241912264811231919/242000000000000000 : ℝ)*(X 0 2+X 1 2)+(544493748967/278300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (241912264811231919/242000000000000000 : ℝ)) (alpha := (544493748967/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1110310709/5000000000 : ℝ)*X 0 0+(1348737223/2500000000 : ℝ)*X 0 1+(2631903157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345046901/10000000000 : ℝ)*X 1 0+(-571792107/2500000000 : ℝ)*X 1 1+(1315951613/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672523451/5000000000 : ℝ)*X 2 0+(2631903187/5000000000 : ℝ)*X 2 1+(-228716853/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((219020231/500000000 : ℝ)*X 0 0+(1063665083/2500000000 : ℝ)*X 0 1+(4509947763/10000000000 : ℝ)*X 0 2+(219020231/500000000 : ℝ)*X 1 0+(1063665083/2500000000 : ℝ)*X 1 1+(4509947763/10000000000 : ℝ)*X 1 2+(219020231/500000000 : ℝ)*X 2 0+(1063665083/2500000000 : ℝ)*X 2 1+(4509947763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1110313287/5000000000 : ℝ)*X 0 0+(5264134411/10000000000 : ℝ)*X 0 1+(5394619613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312105411/10000000000 : ℝ)*X 1 0+(-1078177561/5000000000 : ℝ)*X 1 1+(2697309789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656052631/5000000000 : ℝ)*X 2 0+(107892391/200000000 : ℝ)*X 2 1+(-1078177681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1095103593/2500000000 : ℝ)*X 0 0+(2254654591/5000000000 : ℝ)*X 0 1+(4255301491/10000000000 : ℝ)*X 0 2+(1095103593/2500000000 : ℝ)*X 1 0+(2254654591/5000000000 : ℝ)*X 1 1+(4255301491/10000000000 : ℝ)*X 1 2+(1095103593/2500000000 : ℝ)*X 2 0+(2254654591/5000000000 : ℝ)*X 2 1+(4255301491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1096931857340231972575439691/278300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9564971/2500000000000 : ℝ)*(base19) + (25606111/6250000000000 : ℝ)*(base23) + (3938651/20000000000000 : ℝ)*(lower2) + (139230091/100000000000000 : ℝ)*(upper3) + (522113/1562500000000 : ℝ)*(lower4) + (5771242300659519/100000000000000 : ℝ)*(major0) + (5771242300659519/100000000000000 : ℝ)*(major1) + (5771242300659519/100000000000000 : ℝ)*(major2) + (476581676163833/6250000000000 : ℝ)*(sp0) + (3812658844561347/50000000000000 : ℝ)*(sp1) + (3812658831011879/50000000000000 : ℝ)*(sp2) + (97928962471707/2500000000000 : ℝ)*(sp3) + (5626550103/50000000000000 : ℝ)*(sp4) + (7899344399/100000000000000 : ℝ)*(sp7) + (3917166398212679/100000000000000 : ℝ)*(f.failure) + (3812659035860767/50000000000000 : ℝ)*(f.sum) + (49559153134673/13915000000000000000000000000 : ℝ)*base65 + (426532541697160103/556600000000000000000000000000000 : ℝ)*base67 + (1404276139853760103/556600000000000000000000000000000 : ℝ)*base69 + (1380263139116039897/556600000000000000000000000000000 : ℝ)*base72 + (55945346844283/13915000000000000000000000000 : ℝ)*base73 + (12840504561594960103/556600000000000000000000000000000 : ℝ)*base75 + (3481331525601239897/556600000000000000000000000000000 : ℝ)*base78 + (4989051620947160103/556600000000000000000000000000000 : ℝ)*base79 + (25808699045181/6957500000000000000000000000 : ℝ)*base82 + (897149/10000000000000000000000 : ℝ)*base90 + (897149/10000000000000000000000 : ℝ)*base92 + (897149/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16689468374621401834101813/6050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (464591/160000000000 : ℝ)*(base19) + (126851153/100000000000000 : ℝ)*(base23) + (67682539/100000000000000 : ℝ)*(upper2) + (6250773/100000000000000 : ℝ)*(lower3) + (5887661/50000000000000 : ℝ)*(lower5) + (5800296429320009/100000000000000 : ℝ)*(major0) + (5800296429320009/100000000000000 : ℝ)*(major1) + (5800296429320009/100000000000000 : ℝ)*(major2) + (1800369271/50000000000000 : ℝ)*(sp0) + (12250788353/100000000000000 : ℝ)*(sp1) + (3831851300839913/50000000000000 : ℝ)*(sp4) + (7663693661260639/100000000000000 : ℝ)*(sp5) + (1532741215113443/20000000000000 : ℝ)*(sp6) + (787377312853729/20000000000000 : ℝ)*(sp7) + (787377312853729/20000000000000 : ℝ)*(f.failure) + (119745409412787/1562500000000 : ℝ)*(f.sum) + (10635578843139/605000000000000000000000000 : ℝ)*base66 + (440043506678612729/24200000000000000000000000000000 : ℝ)*base68 + (24948727201187271/24200000000000000000000000000000 : ℝ)*base69 + (160319125703012729/24200000000000000000000000000000 : ℝ)*base72 + (1226896591379/605000000000000000000000000 : ℝ)*base74 + (202271422201212729/24200000000000000000000000000000 : ℝ)*base76 + (158223977984612729/24200000000000000000000000000000 : ℝ)*base78 + (909096746938612729/24200000000000000000000000000000 : ℝ)*base80 + (19282071041/151250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7935301/2000000000000000000000 : ℝ)*base89 + (7935301/2000000000000000000000 : ℝ)*base91 + (7935301/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1032_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1032_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1032_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1032_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1032_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2801/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
