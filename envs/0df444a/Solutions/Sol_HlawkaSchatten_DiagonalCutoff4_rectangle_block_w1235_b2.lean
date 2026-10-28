-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:16:33.263917+00:00
-- url     : https://prove2.me/submissions/e79eda33-b5cf-48d3-af1b-f974797fb2da

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
theorem support_rectangle_w1235_s6_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-530792951/2500000000 : ℝ)*x 0 + (5391526793/10000000000 : ℝ)*x 1 + (5266933081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530792951/2500000000 : ℝ)^2107 ≤ (806910329381/6250000000000 : ℝ)^1595 := by
    have hnat : (530792951 : ℕ)^2107*6250000000000^1595 ≤ 806910329381^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530792951 2500000000 806910329381 6250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391526793/10000000000 : ℝ)^2107 ≤ (4421711511143/10000000000000 : ℝ)^1595 := by
    have hnat : (5391526793 : ℕ)^2107*10000000000000^1595 ≤ 4421711511143^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391526793 10000000000 4421711511143 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266933081/10000000000 : ℝ)^2107 ≤ (42872319597583/100000000000000 : ℝ)^1595 := by
    have hnat : (5266933081 : ℕ)^2107*100000000000000^1595 ≤ 42872319597583^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266933081 10000000000 42872319597583 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530792951/2500000000 : ℝ), (5391526793/10000000000 : ℝ), (5266933081/10000000000 : ℝ)] ![(806910329381/6250000000000 : ℝ), (4421711511143/10000000000000 : ℝ), (42872319597583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530792951/2500000000 : ℝ)|^2107 ≤ (806910329381/6250000000000 : ℝ)^1595
        have hw : |(-530792951/2500000000 : ℝ)|=(530792951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391526793/10000000000 : ℝ)|^2107 ≤ (4421711511143/10000000000000 : ℝ)^1595
        have hw : |(5391526793/10000000000 : ℝ)|=(5391526793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266933081/10000000000 : ℝ)|^2107 ≤ (42872319597583/100000000000000 : ℝ)^1595
        have hw : |(5266933081/10000000000 : ℝ)|=(5266933081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344396121/10000000000 : ℝ)*x 0 + (-2186348257/10000000000 : ℝ)*x 1 + (1053386627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344396121/10000000000 : ℝ)^2107 ≤ (43707226698251/100000000000000 : ℝ)^1595 := by
    have hnat : (5344396121 : ℕ)^2107*100000000000000^1595 ≤ 43707226698251^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344396121 10000000000 43707226698251 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186348257/10000000000 : ℝ)^2107 ≤ (335511327827/2500000000000 : ℝ)^1595 := by
    have hnat : (2186348257 : ℕ)^2107*2500000000000^1595 ≤ 335511327827^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186348257 10000000000 335511327827 2500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053386627/2000000000 : ℝ)^2107 ≤ (42872320178237/100000000000000 : ℝ)^1595 := by
    have hnat : (1053386627 : ℕ)^2107*100000000000000^1595 ≤ 42872320178237^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053386627 2000000000 42872320178237 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344396121/10000000000 : ℝ), (-2186348257/10000000000 : ℝ), (1053386627/2000000000 : ℝ)] ![(43707226698251/100000000000000 : ℝ), (335511327827/2500000000000 : ℝ), (42872320178237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344396121/10000000000 : ℝ)|^2107 ≤ (43707226698251/100000000000000 : ℝ)^1595
        have hw : |(5344396121/10000000000 : ℝ)|=(5344396121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186348257/10000000000 : ℝ)|^2107 ≤ (335511327827/2500000000000 : ℝ)^1595
        have hw : |(-2186348257/10000000000 : ℝ)|=(2186348257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053386627/2000000000 : ℝ)|^2107 ≤ (42872320178237/100000000000000 : ℝ)^1595
        have hw : |(1053386627/2000000000 : ℝ)|=(1053386627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344396013/10000000000 : ℝ)*x 0 + (5266933139/10000000000 : ℝ)*x 1 + (-437269679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344396013/10000000000 : ℝ)^2107 ≤ (4370722553149/10000000000000 : ℝ)^1595 := by
    have hnat : (5344396013 : ℕ)^2107*10000000000000^1595 ≤ 4370722553149^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344396013 10000000000 4370722553149 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266933139/10000000000 : ℝ)^2107 ≤ (669880003457/1562500000000 : ℝ)^1595 := by
    have hnat : (5266933139 : ℕ)^2107*1562500000000^1595 ≤ 669880003457^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266933139 10000000000 669880003457 1562500000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437269679/2000000000 : ℝ)^2107 ≤ (6710227116041/50000000000000 : ℝ)^1595 := by
    have hnat : (437269679 : ℕ)^2107*50000000000000^1595 ≤ 6710227116041^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437269679 2000000000 6710227116041 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344396013/10000000000 : ℝ), (5266933139/10000000000 : ℝ), (-437269679/2000000000 : ℝ)] ![(4370722553149/10000000000000 : ℝ), (669880003457/1562500000000 : ℝ), (6710227116041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344396013/10000000000 : ℝ)|^2107 ≤ (4370722553149/10000000000000 : ℝ)^1595
        have hw : |(5344396013/10000000000 : ℝ)|=(5344396013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266933139/10000000000 : ℝ)|^2107 ≤ (669880003457/1562500000000 : ℝ)^1595
        have hw : |(5266933139/10000000000 : ℝ)|=(5266933139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437269679/2000000000 : ℝ)|^2107 ≤ (6710227116041/50000000000000 : ℝ)^1595
        have hw : |(-437269679/2000000000 : ℝ)|=(437269679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351724109/10000000000 : ℝ)*x 0 + (4227303759/10000000000 : ℝ)*x 1 + (4479709183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351724109/10000000000 : ℝ)^2107 ≤ (6663470996361/20000000000000 : ℝ)^1595 := by
    have hnat : (4351724109 : ℕ)^2107*20000000000000^1595 ≤ 6663470996361^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351724109 10000000000 6663470996361 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227303759/10000000000 : ℝ)^2107 ≤ (320648086751/1000000000000 : ℝ)^1595 := by
    have hnat : (4227303759 : ℕ)^2107*1000000000000^1595 ≤ 320648086751^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227303759 10000000000 320648086751 1000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479709183/10000000000 : ℝ)^2107 ≤ (34617836336629/100000000000000 : ℝ)^1595 := by
    have hnat : (4479709183 : ℕ)^2107*100000000000000^1595 ≤ 34617836336629^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479709183 10000000000 34617836336629 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351724109/10000000000 : ℝ), (4227303759/10000000000 : ℝ), (4479709183/10000000000 : ℝ)] ![(6663470996361/20000000000000 : ℝ), (320648086751/1000000000000 : ℝ), (34617836336629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351724109/10000000000 : ℝ)|^2107 ≤ (6663470996361/20000000000000 : ℝ)^1595
        have hw : |(4351724109/10000000000 : ℝ)|=(4351724109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227303759/10000000000 : ℝ)|^2107 ≤ (320648086751/1000000000000 : ℝ)^1595
        have hw : |(4227303759/10000000000 : ℝ)|=(4227303759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479709183/10000000000 : ℝ)|^2107 ≤ (34617836336629/100000000000000 : ℝ)^1595
        have hw : |(4479709183/10000000000 : ℝ)|=(4479709183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061588349/5000000000 : ℝ)*x 0 + (5267247823/10000000000 : ℝ)*x 1 + (5391210771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061588349/5000000000 : ℝ)^2107 ≤ (3227651145591/25000000000000 : ℝ)^1595 := by
    have hnat : (1061588349 : ℕ)^2107*25000000000000^1595 ≤ 3227651145591^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061588349 5000000000 3227651145591 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267247823/10000000000 : ℝ)^2107 ≤ (5359462999901/12500000000000 : ℝ)^1595 := by
    have hnat : (5267247823 : ℕ)^2107*12500000000000^1595 ≤ 5359462999901^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267247823 10000000000 5359462999901 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391210771/10000000000 : ℝ)^2107 ≤ (22106845705663/50000000000000 : ℝ)^1595 := by
    have hnat : (5391210771 : ℕ)^2107*50000000000000^1595 ≤ 22106845705663^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391210771 10000000000 22106845705663 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061588349/5000000000 : ℝ), (5267247823/10000000000 : ℝ), (5391210771/10000000000 : ℝ)] ![(3227651145591/25000000000000 : ℝ), (5359462999901/12500000000000 : ℝ), (22106845705663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061588349/5000000000 : ℝ)|^2107 ≤ (3227651145591/25000000000000 : ℝ)^1595
        have hw : |(-1061588349/5000000000 : ℝ)|=(1061588349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267247823/10000000000 : ℝ)|^2107 ≤ (5359462999901/12500000000000 : ℝ)^1595
        have hw : |(5267247823/10000000000 : ℝ)|=(5267247823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391210771/10000000000 : ℝ)|^2107 ≤ (22106845705663/50000000000000 : ℝ)^1595
        have hw : |(5391210771/10000000000 : ℝ)|=(5391210771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312620683/10000000000 : ℝ)*x 0 + (-6443973/31250000 : ℝ)*x 1 + (5391210043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312620683/10000000000 : ℝ)^2107 ≤ (2710267095993/6250000000000 : ℝ)^1595 := by
    have hnat : (5312620683 : ℕ)^2107*6250000000000^1595 ≤ 2710267095993^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312620683 10000000000 2710267095993 6250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6443973/31250000 : ℝ)^2107 ≤ (12422042920797/100000000000000 : ℝ)^1595 := by
    have hnat : (6443973 : ℕ)^2107*100000000000000^1595 ≤ 12422042920797^1595*31250000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6443973 31250000 12422042920797 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391210043/10000000000 : ℝ)^2107 ≤ (22106841762219/50000000000000 : ℝ)^1595 := by
    have hnat : (5391210043 : ℕ)^2107*50000000000000^1595 ≤ 22106841762219^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391210043 10000000000 22106841762219 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312620683/10000000000 : ℝ), (-6443973/31250000 : ℝ), (5391210043/10000000000 : ℝ)] ![(2710267095993/6250000000000 : ℝ), (12422042920797/100000000000000 : ℝ), (22106841762219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312620683/10000000000 : ℝ)|^2107 ≤ (2710267095993/6250000000000 : ℝ)^1595
        have hw : |(5312620683/10000000000 : ℝ)|=(5312620683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6443973/31250000 : ℝ)|^2107 ≤ (12422042920797/100000000000000 : ℝ)^1595
        have hw : |(-6443973/31250000 : ℝ)|=(6443973/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391210043/10000000000 : ℝ)|^2107 ≤ (22106841762219/50000000000000 : ℝ)^1595
        have hw : |(5391210043/10000000000 : ℝ)|=(5391210043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312620359/10000000000 : ℝ)*x 0 + (5391210531/10000000000 : ℝ)*x 1 + (-64439723/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312620359/10000000000 : ℝ)^2107 ≤ (43364270042297/100000000000000 : ℝ)^1595 := by
    have hnat : (5312620359 : ℕ)^2107*100000000000000^1595 ≤ 43364270042297^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312620359 10000000000 43364270042297 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391210531/10000000000 : ℝ)^2107 ≤ (44213688811253/100000000000000 : ℝ)^1595 := by
    have hnat : (5391210531 : ℕ)^2107*100000000000000^1595 ≤ 44213688811253^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391210531 10000000000 44213688811253 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64439723/312500000 : ℝ)^2107 ≤ (49688164553/400000000000 : ℝ)^1595 := by
    have hnat : (64439723 : ℕ)^2107*400000000000^1595 ≤ 49688164553^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64439723 312500000 49688164553 400000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312620359/10000000000 : ℝ), (5391210531/10000000000 : ℝ), (-64439723/312500000 : ℝ)] ![(43364270042297/100000000000000 : ℝ), (44213688811253/100000000000000 : ℝ), (49688164553/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312620359/10000000000 : ℝ)|^2107 ≤ (43364270042297/100000000000000 : ℝ)^1595
        have hw : |(5312620359/10000000000 : ℝ)|=(5312620359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391210531/10000000000 : ℝ)|^2107 ≤ (44213688811253/100000000000000 : ℝ)^1595
        have hw : |(5391210531/10000000000 : ℝ)|=(5391210531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64439723/312500000 : ℝ)|^2107 ≤ (49688164553/400000000000 : ℝ)^1595
        have hw : |(-64439723/312500000 : ℝ)|=(64439723/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s6_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1087933613/2500000000 : ℝ)*x 0 + (4479070809/10000000000 : ℝ)*x 1 + (2113971829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087933613/2500000000 : ℝ)^2107 ≤ (33317459588553/100000000000000 : ℝ)^1595 := by
    have hnat : (1087933613 : ℕ)^2107*100000000000000^1595 ≤ 33317459588553^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087933613 2500000000 33317459588553 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479070809/10000000000 : ℝ)^2107 ≤ (34611319764533/100000000000000 : ℝ)^1595 := by
    have hnat : (4479070809 : ℕ)^2107*100000000000000^1595 ≤ 34611319764533^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479070809 10000000000 34611319764533 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113971829/5000000000 : ℝ)^2107 ≤ (16035610319199/50000000000000 : ℝ)^1595 := by
    have hnat : (2113971829 : ℕ)^2107*50000000000000^1595 ≤ 16035610319199^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113971829 5000000000 16035610319199 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087933613/2500000000 : ℝ), (4479070809/10000000000 : ℝ), (2113971829/5000000000 : ℝ)] ![(33317459588553/100000000000000 : ℝ), (34611319764533/100000000000000 : ℝ), (16035610319199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087933613/2500000000 : ℝ)|^2107 ≤ (33317459588553/100000000000000 : ℝ)^1595
        have hw : |(1087933613/2500000000 : ℝ)|=(1087933613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479070809/10000000000 : ℝ)|^2107 ≤ (34611319764533/100000000000000 : ℝ)^1595
        have hw : |(4479070809/10000000000 : ℝ)|=(4479070809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113971829/5000000000 : ℝ)|^2107 ≤ (16035610319199/50000000000000 : ℝ)^1595
        have hw : |(2113971829/5000000000 : ℝ)|=(2113971829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5733/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2289/20000 : ℝ) ^ (8427/2048 : ℝ) ≤ (13379596863351773/100000000000000000000 : ℝ) := by
    have hpowers : (2289/20000 : ℝ)^8427 ≤ (13379596863351773/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2289 : ℕ)^8427*100000000000000000000^2048 ≤ 13379596863351773^2048*20000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 20000 13379596863351773 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/20000 : ℝ)) (X := (13379596863351773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14127/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (15908943384591937/50000000000000000000 : ℝ) := by
    have hpowers : (14127/100000 : ℝ)^8427 ≤ (15908943384591937/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14127 : ℕ)^8427*50000000000000000000^2048 ≤ 15908943384591937^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14127 100000 15908943384591937 50000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14127/100000 : ℝ)) (X := (15908943384591937/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013379596863351773/50000000000000000000 : ℝ) ≤ (2500162564611383/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50013379596863351773/50000000000000000000 : ℝ)^2048 ≤ (2500162564611383/2500000000000000 : ℝ)^8427 := by
      have hnat : (50013379596863351773 : ℕ)^2048*2500000000000000^8427 ≤ 2500162564611383^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013379596863351773 50000000000000000000 2500162564611383 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162564611383/2500000000000000 : ℝ)) (X := (50013379596863351773/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045197483632535647/100000000000000000000 : ℝ) ≤ (10001098239183979/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100045197483632535647/100000000000000000000 : ℝ)^2048 ≤ (10001098239183979/10000000000000000 : ℝ)^8427 := by
      have hnat : (100045197483632535647 : ℕ)^2048*10000000000000000^8427 ≤ 10001098239183979^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045197483632535647 100000000000000000000 10001098239183979 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001098239183979/10000000000000000 : ℝ)) (X := (100045197483632535647/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015908943384591937/25000000000000000000 : ℝ) ≤ (5000773109961213/5000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25015908943384591937/25000000000000000000 : ℝ)^2048 ≤ (5000773109961213/5000000000000000 : ℝ)^8427 := by
      have hnat : (25015908943384591937 : ℕ)^2048*5000000000000000^8427 ≤ 5000773109961213^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015908943384591937 25000000000000000000 5000773109961213 5000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000773109961213/5000000000000000 : ℝ)) (X := (25015908943384591937/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13379596863351773/100000000000000000000 : ℝ) ≤ ((4468581619007977499/4470000000000000000 : ℝ)+2*(447980738447/268200000000000 : ℝ)*(2289/20000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (4468581619007977499/4470000000000000000 : ℝ)+2*(447980738447/268200000000000 : ℝ)*(2289/20000 : ℝ)=(2500162564611383/2500000000000000 : ℝ) by norm_num, show 1+2*(13379596863351773/100000000000000000000 : ℝ)=(50013379596863351773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15908943384591937/50000000000000000000 : ℝ)+(13379596863351773/100000000000000000000 : ℝ) ≤ ((4468581619007977499/4470000000000000000 : ℝ)+(447980738447/268200000000000 : ℝ)*((14127/100000 : ℝ)+(2289/20000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (4468581619007977499/4470000000000000000 : ℝ)+(447980738447/268200000000000 : ℝ)*((14127/100000 : ℝ)+(2289/20000 : ℝ))=(10001098239183979/10000000000000000 : ℝ) by norm_num, show 1+(15908943384591937/50000000000000000000 : ℝ)+(13379596863351773/100000000000000000000 : ℝ)=(100045197483632535647/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15908943384591937/50000000000000000000 : ℝ) ≤ ((4468581619007977499/4470000000000000000 : ℝ)+2*(447980738447/268200000000000 : ℝ)*(14127/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (4468581619007977499/4470000000000000000 : ℝ)+2*(447980738447/268200000000000 : ℝ)*(14127/100000 : ℝ)=(5000773109961213/5000000000000000 : ℝ) by norm_num, show 1+2*(15908943384591937/50000000000000000000 : ℝ)=(25015908943384591937/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4468581619007977499/4470000000000000000 : ℝ)*(X 1 0+X 2 0)+(447980738447/268200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14127/100000 : ℝ)) (c := (4468581619007977499/4470000000000000000 : ℝ)) (alpha := (447980738447/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4468581619007977499/4470000000000000000 : ℝ)*(X 0 1+X 2 1)+(447980738447/268200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14127/100000 : ℝ)) (c := (4468581619007977499/4470000000000000000 : ℝ)) (alpha := (447980738447/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4468581619007977499/4470000000000000000 : ℝ)*(X 0 2+X 1 2)+(447980738447/268200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (14127/100000 : ℝ)) (c := (4468581619007977499/4470000000000000000 : ℝ)) (alpha := (447980738447/268200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-530792951/2500000000 : ℝ)*X 0 0+(5391526793/10000000000 : ℝ)*X 0 1+(5266933081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344396121/10000000000 : ℝ)*X 1 0+(-2186348257/10000000000 : ℝ)*X 1 1+(1053386627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344396013/10000000000 : ℝ)*X 2 0+(5266933139/10000000000 : ℝ)*X 2 1+(-437269679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351724109/10000000000 : ℝ)*X 0 0+(4227303759/10000000000 : ℝ)*X 0 1+(4479709183/10000000000 : ℝ)*X 0 2+(4351724109/10000000000 : ℝ)*X 1 0+(4227303759/10000000000 : ℝ)*X 1 1+(4479709183/10000000000 : ℝ)*X 1 2+(4351724109/10000000000 : ℝ)*X 2 0+(4227303759/10000000000 : ℝ)*X 2 1+(4479709183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061588349/5000000000 : ℝ)*X 0 0+(5267247823/10000000000 : ℝ)*X 0 1+(5391210771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312620683/10000000000 : ℝ)*X 1 0+(-6443973/31250000 : ℝ)*X 1 1+(5391210043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312620359/10000000000 : ℝ)*X 2 0+(5391210531/10000000000 : ℝ)*X 2 1+(-64439723/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087933613/2500000000 : ℝ)*X 0 0+(4479070809/10000000000 : ℝ)*X 0 1+(2113971829/5000000000 : ℝ)*X 0 2+(1087933613/2500000000 : ℝ)*X 1 0+(4479070809/10000000000 : ℝ)*X 1 1+(2113971829/5000000000 : ℝ)*X 1 2+(1087933613/2500000000 : ℝ)*X 2 0+(4479070809/10000000000 : ℝ)*X 2 1+(2113971829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (377223171953918668151347071/74500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (371571263/50000000000000 : ℝ)*(base19) + (567881249/100000000000000 : ℝ)*(base23) + (5702739/50000000000000 : ℝ)*(upper2) + (100828583/100000000000000 : ℝ)*(upper3) + (5994023517599571/100000000000000 : ℝ)*(major0) + (5994023517599571/100000000000000 : ℝ)*(major1) + (5994023517599571/100000000000000 : ℝ)*(major2) + (8026118245215879/100000000000000 : ℝ)*(sp0) + (8026141178640687/100000000000000 : ℝ)*(sp1) + (1605227113308033/20000000000000 : ℝ)*(sp2) + (3961891968053211/100000000000000 : ℝ)*(sp3) + (23676567333/100000000000000 : ℝ)*(sp4) + (5787361799/100000000000000 : ℝ)*(sp6) + (1297658277/10000000000000 : ℝ)*(sp7) + (3961904944635981/100000000000000 : ℝ)*(f.failure) + (8026141921783213/100000000000000 : ℝ)*(f.sum) + (5930158493917/1490000000000000000000000000 : ℝ)*base66 + (1458986687489667643/149000000000000000000000000000000 : ℝ)*base67 + (726032886019667643/149000000000000000000000000000000 : ℝ)*base69 + (55752971679332357/149000000000000000000000000000000 : ℝ)*base72 + (2201097694107/1490000000000000000000000000 : ℝ)*base74 + (697144607627332357/149000000000000000000000000000000 : ℝ)*base76 + (444730152329667643/149000000000000000000000000000000 : ℝ)*base77 + (634387743887667643/149000000000000000000000000000000 : ℝ)*base79 + (4175708145967/1490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19233603/2500000000000000000000 : ℝ)*base89 + (19233603/2500000000000000000000 : ℝ)*base91 + (19233603/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111466590354861181124133091/37250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (720250361/50000000000000 : ℝ)*(base19) + (676782689/100000000000000 : ℝ)*(base23) + (28873051/20000000000000 : ℝ)*(lower2) + (196959751/100000000000000 : ℝ)*(upper3) + (58355701/20000000000000 : ℝ)*(upper5) + (6024499659539409/100000000000000 : ℝ)*(major0) + (6024499659539409/100000000000000 : ℝ)*(major1) + (6024499659539409/100000000000000 : ℝ)*(major2) + (968292917/10000000000000 : ℝ)*(sp0) + (2624036617/100000000000000 : ℝ)*(sp3) + (252091893661091/3125000000000 : ℝ)*(sp4) + (8066948839583361/100000000000000 : ℝ)*(sp5) + (4033474801650697/50000000000000 : ℝ)*(sp6) + (1991023157605861/50000000000000 : ℝ)*(sp7) + (3982048939248339/100000000000000 : ℝ)*(f.failure) + (8066950280084083/100000000000000 : ℝ)*(f.sum) + (15280067078329/4470000000000000000000000000 : ℝ)*base66 + (51017583516191909/447000000000000000000000000000000 : ℝ)*base68 + (2606277565949808091/447000000000000000000000000000000 : ℝ)*base69 + (1649590772247191909/447000000000000000000000000000000 : ℝ)*base72 + (38257400735329/4470000000000000000000000000 : ℝ)*base74 + (7127623310697191909/447000000000000000000000000000000 : ℝ)*base76 + (141513294948191909/447000000000000000000000000000000 : ℝ)*base78 + (1256921590632191909/447000000000000000000000000000000 : ℝ)*base80 + (17572135845469/4470000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (23974557/2500000000000000000000 : ℝ)*base89 + (23974557/2500000000000000000000 : ℝ)*base91 + (23974557/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1235_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s7_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-530797313/2500000000 : ℝ)*x 0 + (1347830911/2500000000 : ℝ)*x 1 + (1316781181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530797313/2500000000 : ℝ)^2107 ≤ (3227676356403/25000000000000 : ℝ)^1595 := by
    have hnat : (530797313 : ℕ)^2107*25000000000000^1595 ≤ 3227676356403^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530797313 2500000000 3227676356403 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347830911/2500000000 : ℝ)^2107 ≤ (22107457120319/50000000000000 : ℝ)^1595 := by
    have hnat : (1347830911 : ℕ)^2107*50000000000000^1595 ≤ 22107457120319^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347830911 2500000000 22107457120319 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316781181/2500000000 : ℝ)^2107 ≤ (21437190157701/50000000000000 : ℝ)^1595 := by
    have hnat : (1316781181 : ℕ)^2107*50000000000000^1595 ≤ 21437190157701^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316781181 2500000000 21437190157701 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530797313/2500000000 : ℝ), (1347830911/2500000000 : ℝ), (1316781181/2500000000 : ℝ)] ![(3227676356403/25000000000000 : ℝ), (22107457120319/50000000000000 : ℝ), (21437190157701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530797313/2500000000 : ℝ)|^2107 ≤ (3227676356403/25000000000000 : ℝ)^1595
        have hw : |(-530797313/2500000000 : ℝ)|=(530797313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347830911/2500000000 : ℝ)|^2107 ≤ (22107457120319/50000000000000 : ℝ)^1595
        have hw : |(1347830911/2500000000 : ℝ)|=(1347830911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316781181/2500000000 : ℝ)|^2107 ≤ (21437190157701/50000000000000 : ℝ)^1595
        have hw : |(1316781181/2500000000 : ℝ)|=(1316781181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068868901/2000000000 : ℝ)*x 0 + (-54654059/250000000 : ℝ)*x 1 + (210685007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068868901/2000000000 : ℝ)^2107 ≤ (21853334536693/50000000000000 : ℝ)^1595 := by
    have hnat : (1068868901 : ℕ)^2107*50000000000000^1595 ≤ 21853334536693^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068868901 2000000000 21853334536693 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54654059/250000000 : ℝ)^2107 ≤ (13418945749073/100000000000000 : ℝ)^1595 := by
    have hnat : (54654059 : ℕ)^2107*100000000000000^1595 ≤ 13418945749073^1595*250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54654059 250000000 13418945749073 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210685007/400000000 : ℝ)^2107 ≤ (10718596291247/25000000000000 : ℝ)^1595 := by
    have hnat : (210685007 : ℕ)^2107*25000000000000^1595 ≤ 10718596291247^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210685007 400000000 10718596291247 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068868901/2000000000 : ℝ), (-54654059/250000000 : ℝ), (210685007/400000000 : ℝ)] ![(21853334536693/50000000000000 : ℝ), (13418945749073/100000000000000 : ℝ), (10718596291247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068868901/2000000000 : ℝ)|^2107 ≤ (21853334536693/50000000000000 : ℝ)^1595
        have hw : |(1068868901/2000000000 : ℝ)|=(1068868901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54654059/250000000 : ℝ)|^2107 ≤ (13418945749073/100000000000000 : ℝ)^1595
        have hw : |(-54654059/250000000 : ℝ)|=(54654059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210685007/400000000 : ℝ)|^2107 ≤ (10718596291247/25000000000000 : ℝ)^1595
        have hw : |(210685007/400000000 : ℝ)|=(210685007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344344629/10000000000 : ℝ)*x 0 + (5267125039/10000000000 : ℝ)*x 1 + (-1093081187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344344629/10000000000 : ℝ)^2107 ≤ (21853335206499/50000000000000 : ℝ)^1595 := by
    have hnat : (5344344629 : ℕ)^2107*50000000000000^1595 ≤ 21853335206499^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344344629 10000000000 21853335206499 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267125039/10000000000 : ℝ)^2107 ≤ (8574876740517/20000000000000 : ℝ)^1595 := by
    have hnat : (5267125039 : ℕ)^2107*20000000000000^1595 ≤ 8574876740517^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267125039 10000000000 8574876740517 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093081187/5000000000 : ℝ)^2107 ≤ (209671029103/1562500000000 : ℝ)^1595 := by
    have hnat : (1093081187 : ℕ)^2107*1562500000000^1595 ≤ 209671029103^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093081187 5000000000 209671029103 1562500000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344344629/10000000000 : ℝ), (5267125039/10000000000 : ℝ), (-1093081187/5000000000 : ℝ)] ![(21853335206499/50000000000000 : ℝ), (8574876740517/20000000000000 : ℝ), (209671029103/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344344629/10000000000 : ℝ)|^2107 ≤ (21853335206499/50000000000000 : ℝ)^1595
        have hw : |(5344344629/10000000000 : ℝ)|=(5344344629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267125039/10000000000 : ℝ)|^2107 ≤ (8574876740517/20000000000000 : ℝ)^1595
        have hw : |(5267125039/10000000000 : ℝ)|=(5267125039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093081187/5000000000 : ℝ)|^2107 ≤ (209671029103/1562500000000 : ℝ)^1595
        have hw : |(-1093081187/5000000000 : ℝ)|=(1093081187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351734711/10000000000 : ℝ)*x 0 + (4227702439/10000000000 : ℝ)*x 1 + (223965367/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351734711/10000000000 : ℝ)^2107 ≤ (33317462208021/100000000000000 : ℝ)^1595 := by
    have hnat : (4351734711 : ℕ)^2107*100000000000000^1595 ≤ 33317462208021^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351734711 10000000000 33317462208021 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227702439/10000000000 : ℝ)^2107 ≤ (6413760704269/20000000000000 : ℝ)^1595 := by
    have hnat : (4227702439 : ℕ)^2107*20000000000000^1595 ≤ 6413760704269^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227702439 10000000000 6413760704269 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223965367/500000000 : ℝ)^2107 ≤ (17306867128427/50000000000000 : ℝ)^1595 := by
    have hnat : (223965367 : ℕ)^2107*50000000000000^1595 ≤ 17306867128427^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223965367 500000000 17306867128427 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351734711/10000000000 : ℝ), (4227702439/10000000000 : ℝ), (223965367/500000000 : ℝ)] ![(33317462208021/100000000000000 : ℝ), (6413760704269/20000000000000 : ℝ), (17306867128427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351734711/10000000000 : ℝ)|^2107 ≤ (33317462208021/100000000000000 : ℝ)^1595
        have hw : |(4351734711/10000000000 : ℝ)|=(4351734711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227702439/10000000000 : ℝ)|^2107 ≤ (6413760704269/20000000000000 : ℝ)^1595
        have hw : |(4227702439/10000000000 : ℝ)|=(4227702439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223965367/500000000 : ℝ)|^2107 ≤ (17306867128427/50000000000000 : ℝ)^1595
        have hw : |(223965367/500000000 : ℝ)|=(223965367/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-424638781/2000000000 : ℝ)*x 0 + (2633719589/5000000000 : ℝ)*x 1 + (2695504039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424638781/2000000000 : ℝ)^2107 ≤ (2582148560417/20000000000000 : ℝ)^1595 := by
    have hnat : (424638781 : ℕ)^2107*20000000000000^1595 ≤ 2582148560417^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424638781 2000000000 2582148560417 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633719589/5000000000 : ℝ)^2107 ≤ (21438880829821/50000000000000 : ℝ)^1595 := by
    have hnat : (2633719589 : ℕ)^2107*50000000000000^1595 ≤ 21438880829821^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633719589 5000000000 21438880829821 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695504039/5000000000 : ℝ)^2107 ≤ (5526436940253/12500000000000 : ℝ)^1595 := by
    have hnat : (2695504039 : ℕ)^2107*12500000000000^1595 ≤ 5526436940253^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695504039 5000000000 5526436940253 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424638781/2000000000 : ℝ), (2633719589/5000000000 : ℝ), (2695504039/5000000000 : ℝ)] ![(2582148560417/20000000000000 : ℝ), (21438880829821/50000000000000 : ℝ), (5526436940253/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424638781/2000000000 : ℝ)|^2107 ≤ (2582148560417/20000000000000 : ℝ)^1595
        have hw : |(-424638781/2000000000 : ℝ)|=(424638781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633719589/5000000000 : ℝ)|^2107 ≤ (21438880829821/50000000000000 : ℝ)^1595
        have hw : |(2633719589/5000000000 : ℝ)|=(2633719589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695504039/5000000000 : ℝ)|^2107 ≤ (5526436940253/12500000000000 : ℝ)^1595
        have hw : |(2695504039/5000000000 : ℝ)|=(2695504039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656334899/5000000000 : ℝ)*x 0 + (-1031139103/5000000000 : ℝ)*x 1 + (5391009217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656334899/5000000000 : ℝ)^2107 ≤ (5420600391061/12500000000000 : ℝ)^1595 := by
    have hnat : (2656334899 : ℕ)^2107*12500000000000^1595 ≤ 5420600391061^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656334899 5000000000 5420600391061 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031139103/5000000000 : ℝ)^2107 ≤ (1552961123377/12500000000000 : ℝ)^1595 := by
    have hnat : (1031139103 : ℕ)^2107*12500000000000^1595 ≤ 1552961123377^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031139103 5000000000 1552961123377 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391009217/10000000000 : ℝ)^2107 ≤ (44211507861389/100000000000000 : ℝ)^1595 := by
    have hnat : (5391009217 : ℕ)^2107*100000000000000^1595 ≤ 44211507861389^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391009217 10000000000 44211507861389 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656334899/5000000000 : ℝ), (-1031139103/5000000000 : ℝ), (5391009217/10000000000 : ℝ)] ![(5420600391061/12500000000000 : ℝ), (1552961123377/12500000000000 : ℝ), (44211507861389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656334899/5000000000 : ℝ)|^2107 ≤ (5420600391061/12500000000000 : ℝ)^1595
        have hw : |(2656334899/5000000000 : ℝ)|=(2656334899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031139103/5000000000 : ℝ)|^2107 ≤ (1552961123377/12500000000000 : ℝ)^1595
        have hw : |(-1031139103/5000000000 : ℝ)|=(1031139103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391009217/10000000000 : ℝ)|^2107 ≤ (44211507861389/100000000000000 : ℝ)^1595
        have hw : |(5391009217/10000000000 : ℝ)|=(5391009217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312669839/10000000000 : ℝ)*x 0 + (2695504531/5000000000 : ℝ)*x 1 + (-1031139181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312669839/10000000000 : ℝ)^2107 ≤ (43364803570579/100000000000000 : ℝ)^1595 := by
    have hnat : (5312669839 : ℕ)^2107*100000000000000^1595 ≤ 43364803570579^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312669839 10000000000 43364803570579 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695504531/5000000000 : ℝ)^2107 ≤ (8842301236439/20000000000000 : ℝ)^1595 := by
    have hnat : (2695504531 : ℕ)^2107*20000000000000^1595 ≤ 8842301236439^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695504531 5000000000 8842301236439 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031139181/5000000000 : ℝ)^2107 ≤ (12423690228473/100000000000000 : ℝ)^1595 := by
    have hnat : (1031139181 : ℕ)^2107*100000000000000^1595 ≤ 12423690228473^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031139181 5000000000 12423690228473 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312669839/10000000000 : ℝ), (2695504531/5000000000 : ℝ), (-1031139181/5000000000 : ℝ)] ![(43364803570579/100000000000000 : ℝ), (8842301236439/20000000000000 : ℝ), (12423690228473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312669839/10000000000 : ℝ)|^2107 ≤ (43364803570579/100000000000000 : ℝ)^1595
        have hw : |(5312669839/10000000000 : ℝ)|=(5312669839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695504531/5000000000 : ℝ)|^2107 ≤ (8842301236439/20000000000000 : ℝ)^1595
        have hw : |(2695504531/5000000000 : ℝ)|=(2695504531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031139181/5000000000 : ℝ)|^2107 ≤ (12423690228473/100000000000000 : ℝ)^1595
        have hw : |(-1031139181/5000000000 : ℝ)|=(1031139181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s7_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351743811/10000000000 : ℝ)*x 0 + (2239336831/5000000000 : ℝ)*x 1 + (4228338771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351743811/10000000000 : ℝ)^2107 ≤ (16658777121709/50000000000000 : ℝ)^1595 := by
    have hnat : (4351743811 : ℕ)^2107*50000000000000^1595 ≤ 16658777121709^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351743811 10000000000 16658777121709 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239336831/5000000000 : ℝ)^2107 ≤ (3460726580709/10000000000000 : ℝ)^1595 := by
    have hnat : (2239336831 : ℕ)^2107*10000000000000^1595 ≤ 3460726580709^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239336831 5000000000 3460726580709 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228338771/10000000000 : ℝ)^2107 ≤ (16037589967237/50000000000000 : ℝ)^1595 := by
    have hnat : (4228338771 : ℕ)^2107*50000000000000^1595 ≤ 16037589967237^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228338771 10000000000 16037589967237 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351743811/10000000000 : ℝ), (2239336831/5000000000 : ℝ), (4228338771/10000000000 : ℝ)] ![(16658777121709/50000000000000 : ℝ), (3460726580709/10000000000000 : ℝ), (16037589967237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351743811/10000000000 : ℝ)|^2107 ≤ (16658777121709/50000000000000 : ℝ)^1595
        have hw : |(4351743811/10000000000 : ℝ)|=(4351743811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239336831/5000000000 : ℝ)|^2107 ≤ (3460726580709/10000000000000 : ℝ)^1595
        have hw : |(2239336831/5000000000 : ℝ)|=(2239336831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228338771/10000000000 : ℝ)|^2107 ≤ (16037589967237/50000000000000 : ℝ)^1595
        have hw : |(4228338771/10000000000 : ℝ)|=(4228338771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1147/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5733/50000 : ℝ) ^ (8427/2048 : ℝ) ≤ (13480901756732067/100000000000000000000 : ℝ) := by
    have hpowers : (5733/50000 : ℝ)^8427 ≤ (13480901756732067/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5733 : ℕ)^8427*100000000000000000000^2048 ≤ 13480901756732067^2048*50000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5733 50000 13480901756732067 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5733/50000 : ℝ)) (X := (13480901756732067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (8427/2048 : ℝ) ≤ (15807247425006953/50000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^8427 ≤ (15807247425006953/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8427*50000000000000000000^2048 ≤ 15807247425006953^2048*20000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 15807247425006953 50000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (15807247425006953/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013480901756732067/50000000000000000000 : ℝ) ≤ (2500163795359259/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50013480901756732067/50000000000000000000 : ℝ)^2048 ≤ (2500163795359259/2500000000000000 : ℝ)^8427 := by
      have hnat : (50013480901756732067 : ℕ)^2048*2500000000000000^8427 ≤ 2500163795359259^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013480901756732067 50000000000000000000 2500163795359259 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500163795359259/2500000000000000 : ℝ)) (X := (50013480901756732067/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045095396606745973/100000000000000000000 : ℝ) ≤ (10001095759027257/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100045095396606745973/100000000000000000000 : ℝ)^2048 ≤ (10001095759027257/10000000000000000 : ℝ)^8427 := by
      have hnat : (100045095396606745973 : ℕ)^2048*10000000000000000^8427 ≤ 10001095759027257^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045095396606745973 100000000000000000000 10001095759027257 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001095759027257/10000000000000000 : ℝ)) (X := (100045095396606745973/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015807247425006953/25000000000000000000 : ℝ) ≤ (5000768168308739/5000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25015807247425006953/25000000000000000000 : ℝ)^2048 ≤ (5000768168308739/5000000000000000 : ℝ)^8427 := by
      have hnat : (25015807247425006953 : ℕ)^2048*5000000000000000^8427 ≤ 5000768168308739^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015807247425006953 25000000000000000000 5000768168308739 5000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000768168308739/5000000000000000 : ℝ)) (X := (25015807247425006953/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13480901756732067/100000000000000000000 : ℝ) ≤ ((18119248419308647/18125000000000000 : ℝ)+2*(440577590221/263900000000000 : ℝ)*(5733/50000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (18119248419308647/18125000000000000 : ℝ)+2*(440577590221/263900000000000 : ℝ)*(5733/50000 : ℝ)=(2500163795359259/2500000000000000 : ℝ) by norm_num, show 1+2*(13480901756732067/100000000000000000000 : ℝ)=(50013480901756732067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15807247425006953/50000000000000000000 : ℝ)+(13480901756732067/100000000000000000000 : ℝ) ≤ ((18119248419308647/18125000000000000 : ℝ)+(440577590221/263900000000000 : ℝ)*((2821/20000 : ℝ)+(5733/50000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (18119248419308647/18125000000000000 : ℝ)+(440577590221/263900000000000 : ℝ)*((2821/20000 : ℝ)+(5733/50000 : ℝ))=(10001095759027257/10000000000000000 : ℝ) by norm_num, show 1+(15807247425006953/50000000000000000000 : ℝ)+(13480901756732067/100000000000000000000 : ℝ)=(100045095396606745973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15807247425006953/50000000000000000000 : ℝ) ≤ ((18119248419308647/18125000000000000 : ℝ)+2*(440577590221/263900000000000 : ℝ)*(2821/20000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (18119248419308647/18125000000000000 : ℝ)+2*(440577590221/263900000000000 : ℝ)*(2821/20000 : ℝ)=(5000768168308739/5000000000000000 : ℝ) by norm_num, show 1+2*(15807247425006953/50000000000000000000 : ℝ)=(25015807247425006953/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18119248419308647/18125000000000000 : ℝ)*(X 1 0+X 2 0)+(440577590221/263900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (18119248419308647/18125000000000000 : ℝ)) (alpha := (440577590221/263900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18119248419308647/18125000000000000 : ℝ)*(X 0 1+X 2 1)+(440577590221/263900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (18119248419308647/18125000000000000 : ℝ)) (alpha := (440577590221/263900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18119248419308647/18125000000000000 : ℝ)*(X 0 2+X 1 2)+(440577590221/263900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (18119248419308647/18125000000000000 : ℝ)) (alpha := (440577590221/263900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-530797313/2500000000 : ℝ)*X 0 0+(1347830911/2500000000 : ℝ)*X 0 1+(1316781181/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068868901/2000000000 : ℝ)*X 1 0+(-54654059/250000000 : ℝ)*X 1 1+(210685007/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344344629/10000000000 : ℝ)*X 2 0+(5267125039/10000000000 : ℝ)*X 2 1+(-1093081187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351734711/10000000000 : ℝ)*X 0 0+(4227702439/10000000000 : ℝ)*X 0 1+(223965367/500000000 : ℝ)*X 0 2+(4351734711/10000000000 : ℝ)*X 1 0+(4227702439/10000000000 : ℝ)*X 1 1+(223965367/500000000 : ℝ)*X 1 2+(4351734711/10000000000 : ℝ)*X 2 0+(4227702439/10000000000 : ℝ)*X 2 1+(223965367/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424638781/2000000000 : ℝ)*X 0 0+(2633719589/5000000000 : ℝ)*X 0 1+(2695504039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656334899/5000000000 : ℝ)*X 1 0+(-1031139103/5000000000 : ℝ)*X 1 1+(5391009217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312669839/10000000000 : ℝ)*X 2 0+(2695504531/5000000000 : ℝ)*X 2 1+(-1031139181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351743811/10000000000 : ℝ)*X 0 0+(2239336831/5000000000 : ℝ)*X 0 1+(4228338771/10000000000 : ℝ)*X 0 2+(4351743811/10000000000 : ℝ)*X 1 0+(2239336831/5000000000 : ℝ)*X 1 1+(4228338771/10000000000 : ℝ)*X 1 2+(4351743811/10000000000 : ℝ)*X 2 0+(2239336831/5000000000 : ℝ)*X 2 1+(4228338771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157300734861536466575979/40267944335937500000000000000 : ℝ) := by norm_num
    linear_combination (1411089387/100000000000000 : ℝ)*(base19) + (1213191651/100000000000000 : ℝ)*(base23) + (205604731/100000000000000 : ℝ)*(lower2) + (294570027/100000000000000 : ℝ)*(upper3) + (2749511/12500000000000 : ℝ)*(upper5) + (3006564245162083/50000000000000 : ℝ)*(major0) + (3006564245162083/50000000000000 : ℝ)*(major1) + (3006564245162083/50000000000000 : ℝ)*(major2) + (8051664535602323/100000000000000 : ℝ)*(sp0) + (20129306421577/250000000000 : ℝ)*(sp1) + (1006465345816067/12500000000000 : ℝ)*(sp2) + (1987252360127711/50000000000000 : ℝ)*(sp3) + (7430514733/12500000000000 : ℝ)*(sp4) + (14075230503/50000000000000 : ℝ)*(sp7) + (993633217679107/25000000000000 : ℝ)*(f.failure) + (8051723979720187/100000000000000 : ℝ)*(f.sum) + (38050888027877/6597500000000000000000000000 : ℝ)*base66 + (198614424668258959/82468750000000000000000000000000 : ℝ)*base68 + (434796786322133959/82468750000000000000000000000000 : ℝ)*base70 + (1926849496714696459/82468750000000000000000000000000 : ℝ)*base72 + (4020995976041/3298750000000000000000000000 : ℝ)*base74 + (897308499768991041/82468750000000000000000000000000 : ℝ)*base75 + (1184059992371446459/82468750000000000000000000000000 : ℝ)*base78 + (1090853075665133959/82468750000000000000000000000000 : ℝ)*base80 + (2515943038813/1649375000000000000000000000 : ℝ)*base82 + (4523341/625000000000000000000 : ℝ)*base89 + (4523341/625000000000000000000 : ℝ)*base91 + (4523341/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5082861517083011715028917/906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (659018693/50000000000000 : ℝ)*(base19) + (1568632007/100000000000000 : ℝ)*(base23) + (108482067/50000000000000 : ℝ)*(upper3) + (4411163/5000000000000 : ℝ)*(lower4) + (6043683712597871/100000000000000 : ℝ)*(major0) + (6043683712597871/100000000000000 : ℝ)*(major1) + (6043683712597871/100000000000000 : ℝ)*(major2) + (10592724791/10000000000000 : ℝ)*(sp1) + (54815048921/50000000000000 : ℝ)*(sp2) + (38087114537/100000000000000 : ℝ)*(sp3) + (252894940709943/3125000000000 : ℝ)*(sp4) + (8092530857432881/100000000000000 : ℝ)*(sp5) + (4046263451994163/50000000000000 : ℝ)*(sp6) + (499336381050899/12500000000000 : ℝ)*(sp7) + (3994729135521729/100000000000000 : ℝ)*(f.failure) + (252894940709943/3125000000000 : ℝ)*(f.sum) + (29161949154557/6597500000000000000000000000 : ℝ)*base66 + (2352119071869995117/164937500000000000000000000000000 : ℝ)*base67 + (1483568725655307617/164937500000000000000000000000000 : ℝ)*base69 + (2019866838898245117/164937500000000000000000000000000 : ℝ)*base71 + (9122462157113/1649375000000000000000000000 : ℝ)*base74 + (1634721953613995117/164937500000000000000000000000000 : ℝ)*base75 + (2233720258359745117/164937500000000000000000000000000 : ℝ)*base77 + (1944529361285120117/164937500000000000000000000000000 : ℝ)*base79 + (57409200496449/13195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (14490127/2500000000000000000000 : ℝ)*base89 + (14490127/2500000000000000000000 : ℝ)*base91 + (14490127/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1235_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1147/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s8_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-530797977/2500000000 : ℝ)*x 0 + (5391286151/10000000000 : ℝ)*x 1 + (1053432103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530797977/2500000000 : ℝ)^2107 ≤ (12910726760643/100000000000000 : ℝ)^1595 := by
    have hnat : (530797977 : ℕ)^2107*100000000000000^1595 ≤ 12910726760643^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530797977 2500000000 12910726760643 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391286151/10000000000 : ℝ)^2107 ≤ (22107254026389/50000000000000 : ℝ)^1595 := by
    have hnat : (5391286151 : ℕ)^2107*50000000000000^1595 ≤ 22107254026389^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391286151 10000000000 22107254026389 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053432103/2000000000 : ℝ)^2107 ≤ (10718691293769/25000000000000 : ℝ)^1595 := by
    have hnat : (1053432103 : ℕ)^2107*25000000000000^1595 ≤ 10718691293769^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053432103 2000000000 10718691293769 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530797977/2500000000 : ℝ), (5391286151/10000000000 : ℝ), (1053432103/2000000000 : ℝ)] ![(12910726760643/100000000000000 : ℝ), (22107254026389/50000000000000 : ℝ), (10718691293769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530797977/2500000000 : ℝ)|^2107 ≤ (12910726760643/100000000000000 : ℝ)^1595
        have hw : |(-530797977/2500000000 : ℝ)|=(530797977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391286151/10000000000 : ℝ)|^2107 ≤ (22107254026389/50000000000000 : ℝ)^1595
        have hw : |(5391286151/10000000000 : ℝ)|=(5391286151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053432103/2000000000 : ℝ)|^2107 ≤ (10718691293769/25000000000000 : ℝ)^1595
        have hw : |(1053432103/2000000000 : ℝ)|=(1053432103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672167613/5000000000 : ℝ)*x 0 + (-273265969/1250000000 : ℝ)*x 1 + (2633580297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672167613/5000000000 : ℝ)^2107 ≤ (21853284414719/50000000000000 : ℝ)^1595 := by
    have hnat : (2672167613 : ℕ)^2107*50000000000000^1595 ≤ 21853284414719^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672167613 5000000000 21853284414719 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273265969/1250000000 : ℝ)^2107 ≤ (6709332565631/50000000000000 : ℝ)^1595 := by
    have hnat : (273265969 : ℕ)^2107*50000000000000^1595 ≤ 6709332565631^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273265969 1250000000 6709332565631 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633580297/5000000000 : ℝ)^2107 ≤ (21437383012281/50000000000000 : ℝ)^1595 := by
    have hnat : (2633580297 : ℕ)^2107*50000000000000^1595 ≤ 21437383012281^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633580297 5000000000 21437383012281 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672167613/5000000000 : ℝ), (-273265969/1250000000 : ℝ), (2633580297/5000000000 : ℝ)] ![(21853284414719/50000000000000 : ℝ), (6709332565631/50000000000000 : ℝ), (21437383012281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672167613/5000000000 : ℝ)|^2107 ≤ (21853284414719/50000000000000 : ℝ)^1595
        have hw : |(2672167613/5000000000 : ℝ)|=(2672167613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273265969/1250000000 : ℝ)|^2107 ≤ (6709332565631/50000000000000 : ℝ)^1595
        have hw : |(-273265969/1250000000 : ℝ)|=(273265969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633580297/5000000000 : ℝ)|^2107 ≤ (21437383012281/50000000000000 : ℝ)^1595
        have hw : |(2633580297/5000000000 : ℝ)|=(2633580297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344335267/10000000000 : ℝ)*x 0 + (5267160517/10000000000 : ℝ)*x 1 + (-10930639/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344335267/10000000000 : ℝ)^2107 ≤ (43706569272373/100000000000000 : ℝ)^1595 := by
    have hnat : (5344335267 : ℕ)^2107*100000000000000^1595 ≤ 43706569272373^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344335267 10000000000 43706569272373 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267160517/10000000000 : ℝ)^2107 ≤ (21437382598291/50000000000000 : ℝ)^1595 := by
    have hnat : (5267160517 : ℕ)^2107*50000000000000^1595 ≤ 21437382598291^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267160517 10000000000 21437382598291 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10930639/50000000 : ℝ)^2107 ≤ (3354666380117/25000000000000 : ℝ)^1595 := by
    have hnat : (10930639 : ℕ)^2107*25000000000000^1595 ≤ 3354666380117^1595*50000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10930639 50000000 3354666380117 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344335267/10000000000 : ℝ), (5267160517/10000000000 : ℝ), (-10930639/50000000 : ℝ)] ![(43706569272373/100000000000000 : ℝ), (21437382598291/50000000000000 : ℝ), (3354666380117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344335267/10000000000 : ℝ)|^2107 ≤ (43706569272373/100000000000000 : ℝ)^1595
        have hw : |(5344335267/10000000000 : ℝ)|=(5344335267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267160517/10000000000 : ℝ)|^2107 ≤ (21437382598291/50000000000000 : ℝ)^1595
        have hw : |(5267160517/10000000000 : ℝ)|=(5267160517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10930639/50000000 : ℝ)|^2107 ≤ (3354666380117/25000000000000 : ℝ)^1595
        have hw : |(-10930639/50000000 : ℝ)|=(10930639/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67995877/156250000 : ℝ)*x 0 + (2113888167/5000000000 : ℝ)*x 1 + (4479233399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67995877/156250000 : ℝ)^2107 ≤ (33317476539243/100000000000000 : ℝ)^1595 := by
    have hnat : (67995877 : ℕ)^2107*100000000000000^1595 ≤ 33317476539243^1595*156250000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67995877 156250000 33317476539243 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113888167/5000000000 : ℝ)^2107 ≤ (16034771987997/50000000000000 : ℝ)^1595 := by
    have hnat : (2113888167 : ℕ)^2107*50000000000000^1595 ≤ 16034771987997^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113888167 5000000000 16034771987997 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479233399/10000000000 : ℝ)^2107 ≤ (3461297946777/10000000000000 : ℝ)^1595 := by
    have hnat : (4479233399 : ℕ)^2107*10000000000000^1595 ≤ 3461297946777^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479233399 10000000000 3461297946777 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67995877/156250000 : ℝ), (2113888167/5000000000 : ℝ), (4479233399/10000000000 : ℝ)] ![(33317476539243/100000000000000 : ℝ), (16034771987997/50000000000000 : ℝ), (3461297946777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67995877/156250000 : ℝ)|^2107 ≤ (33317476539243/100000000000000 : ℝ)^1595
        have hw : |(67995877/156250000 : ℝ)|=(67995877/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113888167/5000000000 : ℝ)|^2107 ≤ (16034771987997/50000000000000 : ℝ)^1595
        have hw : |(2113888167/5000000000 : ℝ)|=(2113888167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479233399/10000000000 : ℝ)|^2107 ≤ (3461297946777/10000000000000 : ℝ)^1595
        have hw : |(4479233399/10000000000 : ℝ)|=(4479233399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-26539961/125000000 : ℝ)*x 0 + (1316868267/2500000000 : ℝ)*x 1 + (5390972233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26539961/125000000 : ℝ)^2107 ≤ (6455383349793/50000000000000 : ℝ)^1595 := by
    have hnat : (26539961 : ℕ)^2107*50000000000000^1595 ≤ 6455383349793^1595*125000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26539961 125000000 6455383349793 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316868267/2500000000 : ℝ)^2107 ≤ (42878126084877/100000000000000 : ℝ)^1595 := by
    have hnat : (1316868267 : ℕ)^2107*100000000000000^1595 ≤ 42878126084877^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316868267 2500000000 42878126084877 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390972233/10000000000 : ℝ)^2107 ≤ (44211107195377/100000000000000 : ℝ)^1595 := by
    have hnat : (5390972233 : ℕ)^2107*100000000000000^1595 ≤ 44211107195377^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390972233 10000000000 44211107195377 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26539961/125000000 : ℝ), (1316868267/2500000000 : ℝ), (5390972233/10000000000 : ℝ)] ![(6455383349793/50000000000000 : ℝ), (42878126084877/100000000000000 : ℝ), (44211107195377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26539961/125000000 : ℝ)|^2107 ≤ (6455383349793/50000000000000 : ℝ)^1595
        have hw : |(-26539961/125000000 : ℝ)|=(26539961/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316868267/2500000000 : ℝ)|^2107 ≤ (42878126084877/100000000000000 : ℝ)^1595
        have hw : |(1316868267/2500000000 : ℝ)|=(1316868267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390972233/10000000000 : ℝ)|^2107 ≤ (44211107195377/100000000000000 : ℝ)^1595
        have hw : |(5390972233/10000000000 : ℝ)|=(5390972233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312679211/10000000000 : ℝ)*x 0 + (-2062316013/10000000000 : ℝ)*x 1 + (5390972077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312679211/10000000000 : ℝ)^2107 ≤ (21682452313139/50000000000000 : ℝ)^1595 := by
    have hnat : (5312679211 : ℕ)^2107*50000000000000^1595 ≤ 21682452313139^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312679211 10000000000 21682452313139 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062316013/10000000000 : ℝ)^2107 ≤ (6211994929123/50000000000000 : ℝ)^1595 := by
    have hnat : (2062316013 : ℕ)^2107*50000000000000^1595 ≤ 6211994929123^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062316013 10000000000 6211994929123 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390972077/10000000000 : ℝ)^2107 ≤ (22105552752677/50000000000000 : ℝ)^1595 := by
    have hnat : (5390972077 : ℕ)^2107*50000000000000^1595 ≤ 22105552752677^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390972077 10000000000 22105552752677 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312679211/10000000000 : ℝ), (-2062316013/10000000000 : ℝ), (5390972077/10000000000 : ℝ)] ![(21682452313139/50000000000000 : ℝ), (6211994929123/50000000000000 : ℝ), (22105552752677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312679211/10000000000 : ℝ)|^2107 ≤ (21682452313139/50000000000000 : ℝ)^1595
        have hw : |(5312679211/10000000000 : ℝ)|=(5312679211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062316013/10000000000 : ℝ)|^2107 ≤ (6211994929123/50000000000000 : ℝ)^1595
        have hw : |(-2062316013/10000000000 : ℝ)|=(2062316013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390972077/10000000000 : ℝ)|^2107 ≤ (22105552752677/50000000000000 : ℝ)^1595
        have hw : |(5390972077/10000000000 : ℝ)|=(5390972077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656339657/5000000000 : ℝ)*x 0 + (5390971937/10000000000 : ℝ)*x 1 + (-2062316063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656339657/5000000000 : ℝ)^2107 ≤ (43364905736899/100000000000000 : ℝ)^1595 := by
    have hnat : (2656339657 : ℕ)^2107*100000000000000^1595 ≤ 43364905736899^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656339657 5000000000 43364905736899 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390971937/10000000000 : ℝ)^2107 ≤ (22105551994333/50000000000000 : ℝ)^1595 := by
    have hnat : (5390971937 : ℕ)^2107*50000000000000^1595 ≤ 22105551994333^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390971937 10000000000 22105551994333 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062316063/10000000000 : ℝ)^2107 ≤ (12423990256151/100000000000000 : ℝ)^1595 := by
    have hnat : (2062316063 : ℕ)^2107*100000000000000^1595 ≤ 12423990256151^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062316063 10000000000 12423990256151 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656339657/5000000000 : ℝ), (5390971937/10000000000 : ℝ), (-2062316063/10000000000 : ℝ)] ![(43364905736899/100000000000000 : ℝ), (22105551994333/50000000000000 : ℝ), (12423990256151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656339657/5000000000 : ℝ)|^2107 ≤ (43364905736899/100000000000000 : ℝ)^1595
        have hw : |(2656339657/5000000000 : ℝ)|=(2656339657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390971937/10000000000 : ℝ)|^2107 ≤ (22105551994333/50000000000000 : ℝ)^1595
        have hw : |(5390971937/10000000000 : ℝ)|=(5390971937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062316063/10000000000 : ℝ)|^2107 ≤ (12423990256151/100000000000000 : ℝ)^1595
        have hw : |(-2062316063/10000000000 : ℝ)|=(2062316063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s8_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (870349133/2000000000 : ℝ)*x 0 + (2239299939/5000000000 : ℝ)*x 1 + (2114206029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870349133/2000000000 : ℝ)^2107 ≤ (33317572994373/100000000000000 : ℝ)^1595 := by
    have hnat : (870349133 : ℕ)^2107*100000000000000^1595 ≤ 33317572994373^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870349133 2000000000 33317572994373 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239299939/5000000000 : ℝ)^2107 ≤ (17303256327431/50000000000000 : ℝ)^1595 := by
    have hnat : (2239299939 : ℕ)^2107*50000000000000^1595 ≤ 17303256327431^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239299939 5000000000 17303256327431 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114206029/5000000000 : ℝ)^2107 ≤ (16037957166103/50000000000000 : ℝ)^1595 := by
    have hnat : (2114206029 : ℕ)^2107*50000000000000^1595 ≤ 16037957166103^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114206029 5000000000 16037957166103 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870349133/2000000000 : ℝ), (2239299939/5000000000 : ℝ), (2114206029/5000000000 : ℝ)] ![(33317572994373/100000000000000 : ℝ), (17303256327431/50000000000000 : ℝ), (16037957166103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870349133/2000000000 : ℝ)|^2107 ≤ (33317572994373/100000000000000 : ℝ)^1595
        have hw : |(870349133/2000000000 : ℝ)|=(870349133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239299939/5000000000 : ℝ)|^2107 ≤ (17303256327431/50000000000000 : ℝ)^1595
        have hw : |(2239299939/5000000000 : ℝ)|=(2239299939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114206029/5000000000 : ℝ)|^2107 ≤ (16037957166103/50000000000000 : ℝ)^1595
        have hw : |(2114206029/5000000000 : ℝ)|=(2114206029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1147/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1147/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1147/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1147/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1147/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1147/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1147/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1147/10000 : ℝ) ^ (8427/2048 : ℝ) ≤ (6750131784077057/50000000000000000000 : ℝ) := by
    have hpowers : (1147/10000 : ℝ)^8427 ≤ (6750131784077057/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1147 : ℕ)^8427*50000000000000000000^2048 ≤ 6750131784077057^2048*10000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1147 10000 6750131784077057 50000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1147/10000 : ℝ)) (X := (6750131784077057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (31577620499589023/100000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^8427 ≤ (31577620499589023/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14101 : ℕ)^8427*100000000000000000000^2048 ≤ 31577620499589023^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 31577620499589023 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (31577620499589023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006750131784077057/25000000000000000000 : ℝ) ≤ (2500164030584683/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25006750131784077057/25000000000000000000 : ℝ)^2048 ≤ (2500164030584683/2500000000000000 : ℝ)^8427 := by
      have hnat : (25006750131784077057 : ℕ)^2048*2500000000000000^8427 ≤ 2500164030584683^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006750131784077057 25000000000000000000 2500164030584683 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500164030584683/2500000000000000 : ℝ)) (X := (25006750131784077057/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045077884067743137/100000000000000000000 : ℝ) ≤ (1000109533356809/1000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100045077884067743137/100000000000000000000 : ℝ)^2048 ≤ (1000109533356809/1000000000000000 : ℝ)^8427 := by
      have hnat : (100045077884067743137 : ℕ)^2048*1000000000000000^8427 ≤ 1000109533356809^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045077884067743137 100000000000000000000 1000109533356809 1000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000109533356809/1000000000000000 : ℝ)) (X := (100045077884067743137/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031577620499589023/50000000000000000000 : ℝ) ≤ (1250191818099681/1250000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50031577620499589023/50000000000000000000 : ℝ)^2048 ≤ (1250191818099681/1250000000000000 : ℝ)^8427 := by
      have hnat : (50031577620499589023 : ℕ)^2048*1250000000000000^8427 ≤ 1250191818099681^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031577620499589023 50000000000000000000 1250191818099681 1250000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250191818099681/1250000000000000 : ℝ)) (X := (50031577620499589023/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6750131784077057/50000000000000000000 : ℝ) ≤ ((6575412688067932843/6577500000000000000 : ℝ)+2*(219605614679/131550000000000 : ℝ)*(1147/10000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (6575412688067932843/6577500000000000000 : ℝ)+2*(219605614679/131550000000000 : ℝ)*(1147/10000 : ℝ)=(2500164030584683/2500000000000000 : ℝ) by norm_num, show 1+2*(6750131784077057/50000000000000000000 : ℝ)=(25006750131784077057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31577620499589023/100000000000000000000 : ℝ)+(6750131784077057/50000000000000000000 : ℝ) ≤ ((6575412688067932843/6577500000000000000 : ℝ)+(219605614679/131550000000000 : ℝ)*((14101/100000 : ℝ)+(1147/10000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (6575412688067932843/6577500000000000000 : ℝ)+(219605614679/131550000000000 : ℝ)*((14101/100000 : ℝ)+(1147/10000 : ℝ))=(1000109533356809/1000000000000000 : ℝ) by norm_num, show 1+(31577620499589023/100000000000000000000 : ℝ)+(6750131784077057/50000000000000000000 : ℝ)=(100045077884067743137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31577620499589023/100000000000000000000 : ℝ) ≤ ((6575412688067932843/6577500000000000000 : ℝ)+2*(219605614679/131550000000000 : ℝ)*(14101/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (6575412688067932843/6577500000000000000 : ℝ)+2*(219605614679/131550000000000 : ℝ)*(14101/100000 : ℝ)=(1250191818099681/1250000000000000 : ℝ) by norm_num, show 1+2*(31577620499589023/100000000000000000000 : ℝ)=(50031577620499589023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6575412688067932843/6577500000000000000 : ℝ)*(X 1 0+X 2 0)+(219605614679/131550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (1147/10000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (6575412688067932843/6577500000000000000 : ℝ)) (alpha := (219605614679/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6575412688067932843/6577500000000000000 : ℝ)*(X 0 1+X 2 1)+(219605614679/131550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (1147/10000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (6575412688067932843/6577500000000000000 : ℝ)) (alpha := (219605614679/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6575412688067932843/6577500000000000000 : ℝ)*(X 0 2+X 1 2)+(219605614679/131550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (1147/10000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (6575412688067932843/6577500000000000000 : ℝ)) (alpha := (219605614679/131550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-530797977/2500000000 : ℝ)*X 0 0+(5391286151/10000000000 : ℝ)*X 0 1+(1053432103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672167613/5000000000 : ℝ)*X 1 0+(-273265969/1250000000 : ℝ)*X 1 1+(2633580297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344335267/10000000000 : ℝ)*X 2 0+(5267160517/10000000000 : ℝ)*X 2 1+(-10930639/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67995877/156250000 : ℝ)*X 0 0+(2113888167/5000000000 : ℝ)*X 0 1+(4479233399/10000000000 : ℝ)*X 0 2+(67995877/156250000 : ℝ)*X 1 0+(2113888167/5000000000 : ℝ)*X 1 1+(4479233399/10000000000 : ℝ)*X 1 2+(67995877/156250000 : ℝ)*X 2 0+(2113888167/5000000000 : ℝ)*X 2 1+(4479233399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26539961/125000000 : ℝ)*X 0 0+(1316868267/2500000000 : ℝ)*X 0 1+(5390972233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312679211/10000000000 : ℝ)*X 1 0+(-2062316013/10000000000 : ℝ)*X 1 1+(5390972077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656339657/5000000000 : ℝ)*X 2 0+(5390971937/10000000000 : ℝ)*X 2 1+(-2062316063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870349133/2000000000 : ℝ)*X 0 0+(2239299939/5000000000 : ℝ)*X 0 1+(2114206029/5000000000 : ℝ)*X 0 2+(870349133/2000000000 : ℝ)*X 1 0+(2239299939/5000000000 : ℝ)*X 1 1+(2114206029/5000000000 : ℝ)*X 1 2+(870349133/2000000000 : ℝ)*X 2 0+(2239299939/5000000000 : ℝ)*X 2 1+(2114206029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6576798317627170513389/2192500000000000000000000000 : ℝ) := by norm_num
    linear_combination (133726713/25000000000000 : ℝ)*(base19) + (34125301/6250000000000 : ℝ)*(base23) + (7187747/25000000000000 : ℝ)*(lower2) + (26169647/25000000000000 : ℝ)*(upper3) + (165091/10000000000000 : ℝ)*(lower4) + (6016614247154943/100000000000000 : ℝ)*(major0) + (6016614247154943/100000000000000 : ℝ)*(major1) + (6016614247154943/100000000000000 : ℝ)*(major2) + (8056374389178529/100000000000000 : ℝ)*(sp0) + (8056390987522911/100000000000000 : ℝ)*(sp1) + (8056390976424947/100000000000000 : ℝ)*(sp2) + (497103509570643/12500000000000 : ℝ)*(sp3) + (8566625617/50000000000000 : ℝ)*(sp4) + (2198831409/25000000000000 : ℝ)*(sp7) + (1988418435945391/50000000000000 : ℝ)*(f.failure) + (8056391522429763/100000000000000 : ℝ)*(f.sum) + (2994746050499/2192500000000000000000000000 : ℝ)*base65 + (1364390884106030983/219250000000000000000000000000000 : ℝ)*base67 + (1158724742959469017/219250000000000000000000000000000 : ℝ)*base70 + (651946567968280983/219250000000000000000000000000000 : ℝ)*base71 + (6266282048939/2192500000000000000000000000 : ℝ)*base73 + (2857868651016719017/219250000000000000000000000000000 : ℝ)*base76 + (1560580376669469017/219250000000000000000000000000000 : ℝ)*base78 + (3860508326202030983/219250000000000000000000000000000 : ℝ)*base79 + (7245697424879/2192500000000000000000000000 : ℝ)*base81 + (11774433/1250000000000000000000 : ℝ)*base89 + (11774433/1250000000000000000000 : ℝ)*base91 + (11774433/1250000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57342534445081629757697643/54812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192418041/12500000000000 : ℝ)*(base19) + (103930349/5000000000000 : ℝ)*(base23) + (49989531/10000000000000 : ℝ)*(lower1) + (197383899/100000000000000 : ℝ)*(upper2) + (10409591/12500000000000 : ℝ)*(upper3) + (59652771/25000000000000 : ℝ)*(upper5) + (6047078307863601/100000000000000 : ℝ)*(major0) + (6047078307863601/100000000000000 : ℝ)*(major1) + (6047078307863601/100000000000000 : ℝ)*(major2) + (56348791/3125000000000 : ℝ)*(sp2) + (2024295924938619/25000000000000 : ℝ)*(sp4) + (2024295540102537/25000000000000 : ℝ)*(sp5) + (1012147477248273/12500000000000 : ℝ)*(sp6) + (1998486440550389/50000000000000 : ℝ)*(sp7) + (1998486440550389/50000000000000 : ℝ)*(f.failure) + (2024295924938619/25000000000000 : ℝ)*(f.sum) + (1635671408171/274062500000000000000000000 : ℝ)*base65 + (388843407524365881/219250000000000000000000000000000 : ℝ)*base67 + (14131467688640634119/219250000000000000000000000000000 : ℝ)*base70 + (1563885482236134119/219250000000000000000000000000000 : ℝ)*base72 + (6883946513607/2192500000000000000000000000 : ℝ)*base74 + (3980625156634634119/219250000000000000000000000000000 : ℝ)*base76 + (2917349683537134119/219250000000000000000000000000000 : ℝ)*base78 + (2593742459897634119/219250000000000000000000000000000 : ℝ)*base80 + (16524432096217/2192500000000000000000000000 : ℝ)*base82 + (4756293/1250000000000000000000 : ℝ)*base90 + (4756293/1250000000000000000000 : ℝ)*base92 + (4756293/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1235_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1147/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1235_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1235_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1235_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1235_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
