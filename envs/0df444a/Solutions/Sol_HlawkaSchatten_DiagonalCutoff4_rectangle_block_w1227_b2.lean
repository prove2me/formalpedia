-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1227_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:13:57.262979+00:00
-- url     : https://prove2.me/submissions/f76093c7-53f2-47b3-b368-cf40e938b466

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
theorem support_rectangle_w1227_s6_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126869523/10000000000 : ℝ)*x 0 + (1347922249/2500000000 : ℝ)*x 1 + (5266810811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126869523/10000000000 : ℝ)^2105 ≤ (1616525776017/12500000000000 : ℝ)^1593 := by
    have hnat : (2126869523 : ℕ)^2105*12500000000000^1593 ≤ 1616525776017^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126869523 10000000000 1616525776017 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347922249/2500000000 : ℝ)^2105 ≤ (442078652927/1000000000000 : ℝ)^1593 := by
    have hnat : (1347922249 : ℕ)^2105*1000000000000^1593 ≤ 442078652927^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347922249 2500000000 442078652927 1000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266810811/10000000000 : ℝ)^2105 ≤ (2142996424081/5000000000000 : ℝ)^1593 := by
    have hnat : (5266810811 : ℕ)^2105*5000000000000^1593 ≤ 2142996424081^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266810811 10000000000 2142996424081 5000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126869523/10000000000 : ℝ), (1347922249/2500000000 : ℝ), (5266810811/10000000000 : ℝ)] ![(1616525776017/12500000000000 : ℝ), (442078652927/1000000000000 : ℝ), (2142996424081/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126869523/10000000000 : ℝ)|^2105 ≤ (1616525776017/12500000000000 : ℝ)^1593
        have hw : |(-2126869523/10000000000 : ℝ)|=(2126869523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347922249/2500000000 : ℝ)|^2105 ≤ (442078652927/1000000000000 : ℝ)^1593
        have hw : |(1347922249/2500000000 : ℝ)|=(1347922249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266810811/10000000000 : ℝ)|^2105 ≤ (2142996424081/5000000000000 : ℝ)^1593
        have hw : |(5266810811/10000000000 : ℝ)|=(5266810811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534444033/1000000000 : ℝ)*x 0 + (-438038499/2000000000 : ℝ)*x 1 + (5266810673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534444033/1000000000 : ℝ)^2105 ≤ (43696669431487/100000000000000 : ℝ)^1593 := by
    have hnat : (534444033 : ℕ)^2105*100000000000000^1593 ≤ 43696669431487^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534444033 1000000000 43696669431487 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438038499/2000000000 : ℝ)^2105 ≤ (6721701780531/50000000000000 : ℝ)^1593 := by
    have hnat : (438038499 : ℕ)^2105*50000000000000^1593 ≤ 6721701780531^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438038499 2000000000 6721701780531 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266810673/10000000000 : ℝ)^2105 ≤ (4285992699767/10000000000000 : ℝ)^1593 := by
    have hnat : (5266810673 : ℕ)^2105*10000000000000^1593 ≤ 4285992699767^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266810673 10000000000 4285992699767 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534444033/1000000000 : ℝ), (-438038499/2000000000 : ℝ), (5266810673/10000000000 : ℝ)] ![(43696669431487/100000000000000 : ℝ), (6721701780531/50000000000000 : ℝ), (4285992699767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534444033/1000000000 : ℝ)|^2105 ≤ (43696669431487/100000000000000 : ℝ)^1593
        have hw : |(534444033/1000000000 : ℝ)|=(534444033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438038499/2000000000 : ℝ)|^2105 ≤ (6721701780531/50000000000000 : ℝ)^1593
        have hw : |(-438038499/2000000000 : ℝ)|=(438038499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266810673/10000000000 : ℝ)|^2105 ≤ (4285992699767/10000000000000 : ℝ)^1593
        have hw : |(5266810673/10000000000 : ℝ)|=(5266810673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344440253/10000000000 : ℝ)*x 0 + (210672429/400000000 : ℝ)*x 1 + (-2190192529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344440253/10000000000 : ℝ)^2105 ≤ (43696668599583/100000000000000 : ℝ)^1593 := by
    have hnat : (5344440253 : ℕ)^2105*100000000000000^1593 ≤ 43696668599583^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344440253 10000000000 43696668599583 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210672429/400000000 : ℝ)^2105 ≤ (42859927556839/100000000000000 : ℝ)^1593 := by
    have hnat : (210672429 : ℕ)^2105*100000000000000^1593 ≤ 42859927556839^1593*400000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210672429 400000000 42859927556839 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190192529/10000000000 : ℝ)^2105 ≤ (13443403836829/100000000000000 : ℝ)^1593 := by
    have hnat : (2190192529 : ℕ)^2105*100000000000000^1593 ≤ 13443403836829^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190192529 10000000000 13443403836829 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344440253/10000000000 : ℝ), (210672429/400000000 : ℝ), (-2190192529/10000000000 : ℝ)] ![(43696668599583/100000000000000 : ℝ), (42859927556839/100000000000000 : ℝ), (13443403836829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344440253/10000000000 : ℝ)|^2105 ≤ (43696668599583/100000000000000 : ℝ)^1593
        have hw : |(5344440253/10000000000 : ℝ)|=(5344440253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210672429/400000000 : ℝ)|^2105 ≤ (42859927556839/100000000000000 : ℝ)^1593
        have hw : |(210672429/400000000 : ℝ)|=(210672429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190192529/10000000000 : ℝ)|^2105 ≤ (13443403836829/100000000000000 : ℝ)^1593
        have hw : |(-2190192529/10000000000 : ℝ)|=(2190192529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68012873/156250000 : ℝ)*x 0 + (1057079041/2500000000 : ℝ)*x 1 + (4480907121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68012873/156250000 : ℝ)^2105 ≤ (33317307893323/100000000000000 : ℝ)^1593 := by
    have hnat : (68012873 : ℕ)^2105*100000000000000^1593 ≤ 33317307893323^1593*156250000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68012873 156250000 33317307893323 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057079041/2500000000 : ℝ)^2105 ≤ (16031914107649/50000000000000 : ℝ)^1593 := by
    have hnat : (1057079041 : ℕ)^2105*50000000000000^1593 ≤ 16031914107649^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057079041 2500000000 16031914107649 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480907121/10000000000 : ℝ)^2105 ≤ (34618863877203/100000000000000 : ℝ)^1593 := by
    have hnat : (4480907121 : ℕ)^2105*100000000000000^1593 ≤ 34618863877203^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480907121 10000000000 34618863877203 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68012873/156250000 : ℝ), (1057079041/2500000000 : ℝ), (4480907121/10000000000 : ℝ)] ![(33317307893323/100000000000000 : ℝ), (16031914107649/50000000000000 : ℝ), (34618863877203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68012873/156250000 : ℝ)|^2105 ≤ (33317307893323/100000000000000 : ℝ)^1593
        have hw : |(68012873/156250000 : ℝ)|=(68012873/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057079041/2500000000 : ℝ)|^2105 ≤ (16031914107649/50000000000000 : ℝ)^1593
        have hw : |(1057079041/2500000000 : ℝ)|=(1057079041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480907121/10000000000 : ℝ)|^2105 ≤ (34618863877203/100000000000000 : ℝ)^1593
        have hw : |(4480907121/10000000000 : ℝ)|=(4480907121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126874313/10000000000 : ℝ)*x 0 + (1053425299/2000000000 : ℝ)*x 1 + (5391372123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126874313/10000000000 : ℝ)^2105 ≤ (808265293389/6250000000000 : ℝ)^1593 := by
    have hnat : (2126874313 : ℕ)^2105*6250000000000^1593 ≤ 808265293389^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126874313 10000000000 808265293389 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053425299/2000000000 : ℝ)^2105 ≤ (10715830786419/25000000000000 : ℝ)^1593 := by
    have hnat : (1053425299 : ℕ)^2105*25000000000000^1593 ≤ 10715830786419^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053425299 2000000000 10715830786419 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391372123/10000000000 : ℝ)^2105 ≤ (44204432147521/100000000000000 : ℝ)^1593 := by
    have hnat : (5391372123 : ℕ)^2105*100000000000000^1593 ≤ 44204432147521^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391372123 10000000000 44204432147521 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126874313/10000000000 : ℝ), (1053425299/2000000000 : ℝ), (5391372123/10000000000 : ℝ)] ![(808265293389/6250000000000 : ℝ), (10715830786419/25000000000000 : ℝ), (44204432147521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126874313/10000000000 : ℝ)|^2105 ≤ (808265293389/6250000000000 : ℝ)^1593
        have hw : |(-2126874313/10000000000 : ℝ)|=(2126874313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053425299/2000000000 : ℝ)|^2105 ≤ (10715830786419/25000000000000 : ℝ)^1593
        have hw : |(1053425299/2000000000 : ℝ)|=(1053425299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391372123/10000000000 : ℝ)|^2105 ≤ (44204432147521/100000000000000 : ℝ)^1593
        have hw : |(5391372123/10000000000 : ℝ)|=(5391372123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062521909/2000000000 : ℝ)*x 0 + (-1032815561/5000000000 : ℝ)*x 1 + (5391372071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062521909/2000000000 : ℝ)^2105 ≤ (21676550464689/50000000000000 : ℝ)^1593 := by
    have hnat : (1062521909 : ℕ)^2105*50000000000000^1593 ≤ 21676550464689^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062521909 2000000000 21676550464689 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032815561/5000000000 : ℝ)^2105 ≤ (12442467479099/100000000000000 : ℝ)^1593 := by
    have hnat : (1032815561 : ℕ)^2105*100000000000000^1593 ≤ 12442467479099^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032815561 5000000000 12442467479099 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391372071/10000000000 : ℝ)^2105 ≤ (22102215792067/50000000000000 : ℝ)^1593 := by
    have hnat : (5391372071 : ℕ)^2105*50000000000000^1593 ≤ 22102215792067^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391372071 10000000000 22102215792067 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062521909/2000000000 : ℝ), (-1032815561/5000000000 : ℝ), (5391372071/10000000000 : ℝ)] ![(21676550464689/50000000000000 : ℝ), (12442467479099/100000000000000 : ℝ), (22102215792067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062521909/2000000000 : ℝ)|^2105 ≤ (21676550464689/50000000000000 : ℝ)^1593
        have hw : |(1062521909/2000000000 : ℝ)|=(1062521909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032815561/5000000000 : ℝ)|^2105 ≤ (12442467479099/100000000000000 : ℝ)^1593
        have hw : |(-1032815561/5000000000 : ℝ)|=(1032815561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391372071/10000000000 : ℝ)|^2105 ≤ (22102215792067/50000000000000 : ℝ)^1593
        have hw : |(5391372071/10000000000 : ℝ)|=(5391372071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328152393/2500000000 : ℝ)*x 0 + (5391372089/10000000000 : ℝ)*x 1 + (-103281553/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328152393/2500000000 : ℝ)^2105 ≤ (1734124048821/4000000000000 : ℝ)^1593 := by
    have hnat : (1328152393 : ℕ)^2105*4000000000000^1593 ≤ 1734124048821^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328152393 2500000000 1734124048821 4000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391372089/10000000000 : ℝ)^2105 ≤ (44204431779153/100000000000000 : ℝ)^1593 := by
    have hnat : (5391372089 : ℕ)^2105*100000000000000^1593 ≤ 44204431779153^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391372089 10000000000 44204431779153 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103281553/500000000 : ℝ)^2105 ≤ (6221233492803/50000000000000 : ℝ)^1593 := by
    have hnat : (103281553 : ℕ)^2105*50000000000000^1593 ≤ 6221233492803^1593*500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103281553 500000000 6221233492803 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328152393/2500000000 : ℝ), (5391372089/10000000000 : ℝ), (-103281553/500000000 : ℝ)] ![(1734124048821/4000000000000 : ℝ), (44204431779153/100000000000000 : ℝ), (6221233492803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328152393/2500000000 : ℝ)|^2105 ≤ (1734124048821/4000000000000 : ℝ)^1593
        have hw : |(1328152393/2500000000 : ℝ)|=(1328152393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391372089/10000000000 : ℝ)|^2105 ≤ (44204431779153/100000000000000 : ℝ)^1593
        have hw : |(5391372089/10000000000 : ℝ)|=(5391372089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103281553/500000000 : ℝ)|^2105 ≤ (6221233492803/50000000000000 : ℝ)^1593
        have hw : |(-103281553/500000000 : ℝ)|=(103281553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s6_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352833639/10000000000 : ℝ)*x 0 + (448026833/1000000000 : ℝ)*x 1 + (422895709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352833639/10000000000 : ℝ)^2105 ≤ (2082337917473/6250000000000 : ℝ)^1593 := by
    have hnat : (4352833639 : ℕ)^2105*6250000000000^1593 ≤ 2082337917473^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352833639 10000000000 2082337917473 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448026833/1000000000 : ℝ)^2105 ≤ (4326542826181/12500000000000 : ℝ)^1593 := by
    have hnat : (448026833 : ℕ)^2105*12500000000000^1593 ≤ 4326542826181^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448026833 1000000000 4326542826181 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422895709/1000000000 : ℝ)^2105 ≤ (16035125347293/50000000000000 : ℝ)^1593 := by
    have hnat : (422895709 : ℕ)^2105*50000000000000^1593 ≤ 16035125347293^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422895709 1000000000 16035125347293 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352833639/10000000000 : ℝ), (448026833/1000000000 : ℝ), (422895709/1000000000 : ℝ)] ![(2082337917473/6250000000000 : ℝ), (4326542826181/12500000000000 : ℝ), (16035125347293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352833639/10000000000 : ℝ)|^2105 ≤ (2082337917473/6250000000000 : ℝ)^1593
        have hw : |(4352833639/10000000000 : ℝ)|=(4352833639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448026833/1000000000 : ℝ)|^2105 ≤ (4326542826181/12500000000000 : ℝ)^1593
        have hw : |(448026833/1000000000 : ℝ)|=(448026833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422895709/1000000000 : ℝ)|^2105 ≤ (16035125347293/50000000000000 : ℝ)^1593
        have hw : |(422895709/1000000000 : ℝ)|=(422895709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (358/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5717/50000 : ℝ) ^ (8419/2048 : ℝ) ≤ (1344013360073243/10000000000000000000 : ℝ) := by
    have hpowers : (5717/50000 : ℝ)^8419 ≤ (1344013360073243/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5717 : ℕ)^8419*10000000000000000000^2048 ≤ 1344013360073243^2048*50000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5717 50000 1344013360073243 10000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5717/50000 : ℝ)) (X := (1344013360073243/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3531/25000 : ℝ) ^ (8419/2048 : ℝ) ≤ (16017040922486979/50000000000000000000 : ℝ) := by
    have hpowers : (3531/25000 : ℝ)^8419 ≤ (16017040922486979/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3531 : ℕ)^8419*50000000000000000000^2048 ≤ 16017040922486979^2048*25000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3531 25000 16017040922486979 50000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3531/25000 : ℝ)) (X := (16017040922486979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001344013360073243/5000000000000000000 : ℝ) ≤ (10000653820988971/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (5001344013360073243/5000000000000000000 : ℝ)^2048 ≤ (10000653820988971/10000000000000000 : ℝ)^8419 := by
      have hnat : (5001344013360073243 : ℕ)^2048*10000000000000000^8419 ≤ 10000653820988971^8419*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001344013360073243 5000000000000000000 10000653820988971 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000653820988971/10000000000000000 : ℝ)) (X := (5001344013360073243/5000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011368553861426597/25000000000000000000 : ℝ) ≤ (10001106012272919/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (25011368553861426597/25000000000000000000 : ℝ)^2048 ≤ (10001106012272919/10000000000000000 : ℝ)^8419 := by
      have hnat : (25011368553861426597 : ℕ)^2048*10000000000000000^8419 ≤ 10001106012272919^8419*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011368553861426597 25000000000000000000 10001106012272919 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001106012272919/10000000000000000 : ℝ)) (X := (25011368553861426597/25000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016017040922486979/25000000000000000000 : ℝ) ≤ (10001558203556867/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (25016017040922486979/25000000000000000000 : ℝ)^2048 ≤ (10001558203556867/10000000000000000 : ℝ)^8419 := by
      have hnat : (25016017040922486979 : ℕ)^2048*10000000000000000^8419 ≤ 10001558203556867^8419*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016017040922486979 25000000000000000000 10001558203556867 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001558203556867/10000000000000000 : ℝ)) (X := (25016017040922486979/25000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1344013360073243/10000000000000000000 : ℝ) ≤ ((13445709034089504563/13450000000000000000 : ℝ)+2*(113047820987/67250000000000 : ℝ)*(5717/50000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (13445709034089504563/13450000000000000000 : ℝ)+2*(113047820987/67250000000000 : ℝ)*(5717/50000 : ℝ)=(10000653820988971/10000000000000000 : ℝ) by norm_num, show 1+2*(1344013360073243/10000000000000000000 : ℝ)=(5001344013360073243/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16017040922486979/50000000000000000000 : ℝ)+(1344013360073243/10000000000000000000 : ℝ) ≤ ((13445709034089504563/13450000000000000000 : ℝ)+(113047820987/67250000000000 : ℝ)*((3531/25000 : ℝ)+(5717/50000 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (13445709034089504563/13450000000000000000 : ℝ)+(113047820987/67250000000000 : ℝ)*((3531/25000 : ℝ)+(5717/50000 : ℝ))=(10001106012272919/10000000000000000 : ℝ) by norm_num, show 1+(16017040922486979/50000000000000000000 : ℝ)+(1344013360073243/10000000000000000000 : ℝ)=(25011368553861426597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16017040922486979/50000000000000000000 : ℝ) ≤ ((13445709034089504563/13450000000000000000 : ℝ)+2*(113047820987/67250000000000 : ℝ)*(3531/25000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (13445709034089504563/13450000000000000000 : ℝ)+2*(113047820987/67250000000000 : ℝ)*(3531/25000 : ℝ)=(10001558203556867/10000000000000000 : ℝ) by norm_num, show 1+2*(16017040922486979/50000000000000000000 : ℝ)=(25016017040922486979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13445709034089504563/13450000000000000000 : ℝ)*(X 1 0+X 2 0)+(113047820987/67250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13445709034089504563/13450000000000000000 : ℝ)) (alpha := (113047820987/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13445709034089504563/13450000000000000000 : ℝ)*(X 0 1+X 2 1)+(113047820987/67250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13445709034089504563/13450000000000000000 : ℝ)) (alpha := (113047820987/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13445709034089504563/13450000000000000000 : ℝ)*(X 0 2+X 1 2)+(113047820987/67250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13445709034089504563/13450000000000000000 : ℝ)) (alpha := (113047820987/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2126869523/10000000000 : ℝ)*X 0 0+(1347922249/2500000000 : ℝ)*X 0 1+(5266810811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534444033/1000000000 : ℝ)*X 1 0+(-438038499/2000000000 : ℝ)*X 1 1+(5266810673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344440253/10000000000 : ℝ)*X 2 0+(210672429/400000000 : ℝ)*X 2 1+(-2190192529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68012873/156250000 : ℝ)*X 0 0+(1057079041/2500000000 : ℝ)*X 0 1+(4480907121/10000000000 : ℝ)*X 0 2+(68012873/156250000 : ℝ)*X 1 0+(1057079041/2500000000 : ℝ)*X 1 1+(4480907121/10000000000 : ℝ)*X 1 2+(68012873/156250000 : ℝ)*X 2 0+(1057079041/2500000000 : ℝ)*X 2 1+(4480907121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2126874313/10000000000 : ℝ)*X 0 0+(1053425299/2000000000 : ℝ)*X 0 1+(5391372123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062521909/2000000000 : ℝ)*X 1 0+(-1032815561/5000000000 : ℝ)*X 1 1+(5391372071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328152393/2500000000 : ℝ)*X 2 0+(5391372089/10000000000 : ℝ)*X 2 1+(-103281553/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352833639/10000000000 : ℝ)*X 0 0+(448026833/1000000000 : ℝ)*X 0 1+(422895709/1000000000 : ℝ)*X 0 2+(4352833639/10000000000 : ℝ)*X 1 0+(448026833/1000000000 : ℝ)*X 1 1+(422895709/1000000000 : ℝ)*X 1 2+(4352833639/10000000000 : ℝ)*X 2 0+(448026833/1000000000 : ℝ)*X 2 1+(422895709/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1749160573066840226834348259/336250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777894871/100000000000000 : ℝ)*(base19) + (641992071/100000000000000 : ℝ)*(base23) + (10945221/50000000000000 : ℝ)*(lower2) + (91320093/100000000000000 : ℝ)*(upper3) + (5459167/50000000000000 : ℝ)*(lower4) + (5983412998154869/100000000000000 : ℝ)*(major0) + (5983412998154869/100000000000000 : ℝ)*(major1) + (5983412998154869/100000000000000 : ℝ)*(major2) + (8007822549469509/100000000000000 : ℝ)*(sp0) + (8007835127578957/100000000000000 : ℝ)*(sp1) + (4003917631740879/50000000000000 : ℝ)*(sp2) + (395897921043867/10000000000000 : ℝ)*(sp3) + (83475027/625000000000 : ℝ)*(sp4) + (10706998413/100000000000000 : ℝ)*(sp7) + (3958989917437083/100000000000000 : ℝ)*(f.failure) + (8007835905473829/100000000000000 : ℝ)*(f.sum) + (10842753462047/3362500000000000000000000000 : ℝ)*base66 + (12093911551266767247/1345000000000000000000000000000000 : ℝ)*base67 + (11321347767841767247/1345000000000000000000000000000000 : ℝ)*base69 + (16560148917331767247/1345000000000000000000000000000000 : ℝ)*base71 + (6321946338469/6725000000000000000000000000 : ℝ)*base74 + (25381742524651767247/1345000000000000000000000000000000 : ℝ)*base75 + (4067132839248232753/1345000000000000000000000000000000 : ℝ)*base78 + (18338782616096767247/1345000000000000000000000000000000 : ℝ)*base79 + (4408148102839/1681250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7198777/5000000000000000000000 : ℝ)*base89 + (7198777/5000000000000000000000 : ℝ)*base91 + (7198777/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2480682956675433261464027511/672500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362253891/50000000000000 : ℝ)*(base19) + (45459081/5000000000000 : ℝ)*(base23) + (75133391/100000000000000 : ℝ)*(upper3) + (13301407/25000000000000 : ℝ)*(lower4) + (75359703/100000000000000 : ℝ)*(upper5) + (6013850939363067/100000000000000 : ℝ)*(major0) + (6013850939363067/100000000000000 : ℝ)*(major1) + (6013850939363067/100000000000000 : ℝ)*(major2) + (8707060131/50000000000000 : ℝ)*(sp1) + (6173582873/25000000000000 : ℝ)*(sp2) + (2012143061340337/25000000000000 : ℝ)*(sp4) + (8048554106733303/100000000000000 : ℝ)*(sp5) + (2012136660462059/25000000000000 : ℝ)*(sp6) + (1989564755203253/50000000000000 : ℝ)*(sp7) + (1989564755203253/50000000000000 : ℝ)*(f.failure) + (2012143061340337/25000000000000 : ℝ)*(f.sum) + (3237587011501/840625000000000000000000000 : ℝ)*base65 + (717425693435974721/1345000000000000000000000000000000 : ℝ)*base67 + (13052879198555974721/1345000000000000000000000000000000 : ℝ)*base69 + (8569093606730974721/1345000000000000000000000000000000 : ℝ)*base71 + (1012585635179/3362500000000000000000000000 : ℝ)*base73 + (64192422076480974721/1345000000000000000000000000000000 : ℝ)*base75 + (25885808722545974721/1345000000000000000000000000000000 : ℝ)*base77 + (26520683851255974721/1345000000000000000000000000000000 : ℝ)*base79 + (4886425085529/3362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (25385993/2500000000000000000000 : ℝ)*base90 + (25385993/2500000000000000000000 : ℝ)*base92 + (25385993/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1227_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1227_s7_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-531721887/2500000000 : ℝ)*x 0 + (5391477021/10000000000 : ℝ)*x 1 + (2633505459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531721887/2500000000 : ℝ)^2105 ≤ (12932351033277/100000000000000 : ℝ)^1593 := by
    have hnat : (531721887 : ℕ)^2105*100000000000000^1593 ≤ 12932351033277^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531721887 2500000000 12932351033277 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391477021/10000000000 : ℝ)^2105 ≤ (44205568652643/100000000000000 : ℝ)^1593 := by
    have hnat : (5391477021 : ℕ)^2105*100000000000000^1593 ≤ 44205568652643^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391477021 10000000000 44205568652643 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633505459/5000000000 : ℝ)^2105 ≤ (10715520074217/25000000000000 : ℝ)^1593 := by
    have hnat : (2633505459 : ℕ)^2105*25000000000000^1593 ≤ 10715520074217^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633505459 5000000000 10715520074217 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531721887/2500000000 : ℝ), (5391477021/10000000000 : ℝ), (2633505459/5000000000 : ℝ)] ![(12932351033277/100000000000000 : ℝ), (44205568652643/100000000000000 : ℝ), (10715520074217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531721887/2500000000 : ℝ)|^2105 ≤ (12932351033277/100000000000000 : ℝ)^1593
        have hw : |(-531721887/2500000000 : ℝ)|=(531721887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391477021/10000000000 : ℝ)|^2105 ≤ (44205568652643/100000000000000 : ℝ)^1593
        have hw : |(5391477021/10000000000 : ℝ)|=(5391477021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633505459/5000000000 : ℝ)|^2105 ≤ (10715520074217/25000000000000 : ℝ)^1593
        have hw : |(2633505459/5000000000 : ℝ)|=(2633505459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068876951/2000000000 : ℝ)*x 0 + (-34218681/156250000 : ℝ)*x 1 + (5267015029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068876951/2000000000 : ℝ)^2105 ≤ (1092401725079/2500000000000 : ℝ)^1593 := by
    have hnat : (1068876951 : ℕ)^2105*2500000000000^1593 ≤ 1092401725079^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068876951 2000000000 1092401725079 2500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34218681/156250000 : ℝ)^2105 ≤ (6720903239969/50000000000000 : ℝ)^1593 := by
    have hnat : (34218681 : ℕ)^2105*50000000000000^1593 ≤ 6720903239969^1593*156250000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34218681 156250000 6720903239969 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267015029/10000000000 : ℝ)^2105 ≤ (8572424900811/20000000000000 : ℝ)^1593 := by
    have hnat : (5267015029 : ℕ)^2105*20000000000000^1593 ≤ 8572424900811^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267015029 10000000000 8572424900811 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068876951/2000000000 : ℝ), (-34218681/156250000 : ℝ), (5267015029/10000000000 : ℝ)] ![(1092401725079/2500000000000 : ℝ), (6720903239969/50000000000000 : ℝ), (8572424900811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068876951/2000000000 : ℝ)|^2105 ≤ (1092401725079/2500000000000 : ℝ)^1593
        have hw : |(1068876951/2000000000 : ℝ)|=(1068876951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34218681/156250000 : ℝ)|^2105 ≤ (6720903239969/50000000000000 : ℝ)^1593
        have hw : |(-34218681/156250000 : ℝ)|=(34218681/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267015029/10000000000 : ℝ)|^2105 ≤ (8572424900811/20000000000000 : ℝ)^1593
        have hw : |(5267015029/10000000000 : ℝ)|=(5267015029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344388251/10000000000 : ℝ)*x 0 + (2633506179/5000000000 : ℝ)*x 1 + (-547498617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344388251/10000000000 : ℝ)^2105 ≤ (8739221354727/20000000000000 : ℝ)^1593 := by
    have hnat : (5344388251 : ℕ)^2105*20000000000000^1593 ≤ 8739221354727^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344388251 10000000000 8739221354727 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633506179/5000000000 : ℝ)^2105 ≤ (42862095781749/100000000000000 : ℝ)^1593 := by
    have hnat : (2633506179 : ℕ)^2105*100000000000000^1593 ≤ 42862095781749^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633506179 5000000000 42862095781749 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547498617/2500000000 : ℝ)^2105 ≤ (3360449357139/25000000000000 : ℝ)^1593 := by
    have hnat : (547498617 : ℕ)^2105*25000000000000^1593 ≤ 3360449357139^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547498617 2500000000 3360449357139 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344388251/10000000000 : ℝ), (2633506179/5000000000 : ℝ), (-547498617/2500000000 : ℝ)] ![(8739221354727/20000000000000 : ℝ), (42862095781749/100000000000000 : ℝ), (3360449357139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344388251/10000000000 : ℝ)|^2105 ≤ (8739221354727/20000000000000 : ℝ)^1593
        have hw : |(5344388251/10000000000 : ℝ)|=(5344388251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633506179/5000000000 : ℝ)|^2105 ≤ (42862095781749/100000000000000 : ℝ)^1593
        have hw : |(2633506179/5000000000 : ℝ)|=(2633506179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547498617/2500000000 : ℝ)|^2105 ≤ (3360449357139/25000000000000 : ℝ)^1593
        have hw : |(-547498617/2500000000 : ℝ)|=(547498617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352839943/10000000000 : ℝ)*x 0 + (528591507/1250000000 : ℝ)*x 1 + (4480482977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352839943/10000000000 : ℝ)^2105 ≤ (33317470440073/100000000000000 : ℝ)^1593 := by
    have hnat : (4352839943 : ℕ)^2105*100000000000000^1593 ≤ 33317470440073^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352839943 10000000000 33317470440073 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528591507/1250000000 : ℝ)^2105 ≤ (32067995677553/100000000000000 : ℝ)^1593 := by
    have hnat : (528591507 : ℕ)^2105*100000000000000^1593 ≤ 32067995677553^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528591507 1250000000 32067995677553 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480482977/10000000000 : ℝ)^2105 ≤ (34614533857079/100000000000000 : ℝ)^1593 := by
    have hnat : (4480482977 : ℕ)^2105*100000000000000^1593 ≤ 34614533857079^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480482977 10000000000 34614533857079 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352839943/10000000000 : ℝ), (528591507/1250000000 : ℝ), (4480482977/10000000000 : ℝ)] ![(33317470440073/100000000000000 : ℝ), (32067995677553/100000000000000 : ℝ), (34614533857079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352839943/10000000000 : ℝ)|^2105 ≤ (33317470440073/100000000000000 : ℝ)^1593
        have hw : |(4352839943/10000000000 : ℝ)|=(4352839943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528591507/1250000000 : ℝ)|^2105 ≤ (32067995677553/100000000000000 : ℝ)^1593
        have hw : |(528591507/1250000000 : ℝ)|=(528591507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480482977/10000000000 : ℝ)|^2105 ≤ (34614533857079/100000000000000 : ℝ)^1593
        have hw : |(4480482977/10000000000 : ℝ)|=(4480482977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063446261/5000000000 : ℝ)*x 0 + (2633663281/5000000000 : ℝ)*x 1 + (5391160043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063446261/5000000000 : ℝ)^2105 ≤ (2586478199571/20000000000000 : ℝ)^1593 := by
    have hnat : (1063446261 : ℕ)^2105*20000000000000^1593 ≤ 2586478199571^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063446261 5000000000 2586478199571 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633663281/5000000000 : ℝ)^2105 ≤ (42865474572233/100000000000000 : ℝ)^1593 := by
    have hnat : (2633663281 : ℕ)^2105*100000000000000^1593 ≤ 42865474572233^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633663281 5000000000 42865474572233 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391160043/10000000000 : ℝ)^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593 := by
    have hnat : (5391160043 : ℕ)^2105*20000000000000^1593 ≤ 8840426882651^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391160043 10000000000 8840426882651 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063446261/5000000000 : ℝ), (2633663281/5000000000 : ℝ), (5391160043/10000000000 : ℝ)] ![(2586478199571/20000000000000 : ℝ), (42865474572233/100000000000000 : ℝ), (8840426882651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063446261/5000000000 : ℝ)|^2105 ≤ (2586478199571/20000000000000 : ℝ)^1593
        have hw : |(-1063446261/5000000000 : ℝ)|=(1063446261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633663281/5000000000 : ℝ)|^2105 ≤ (42865474572233/100000000000000 : ℝ)^1593
        have hw : |(2633663281/5000000000 : ℝ)|=(2633663281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391160043/10000000000 : ℝ)|^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593
        have hw : |(5391160043/10000000000 : ℝ)|=(5391160043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656330681/5000000000 : ℝ)*x 0 + (-2065849523/10000000000 : ℝ)*x 1 + (5391160043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656330681/5000000000 : ℝ)^2105 ≤ (2709603730283/6250000000000 : ℝ)^1593 := by
    have hnat : (2656330681 : ℕ)^2105*6250000000000^1593 ≤ 2709603730283^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656330681 5000000000 2709603730283 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065849523/10000000000 : ℝ)^2105 ≤ (622210294427/5000000000000 : ℝ)^1593 := by
    have hnat : (2065849523 : ℕ)^2105*5000000000000^1593 ≤ 622210294427^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065849523 10000000000 622210294427 5000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391160043/10000000000 : ℝ)^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593 := by
    have hnat : (5391160043 : ℕ)^2105*20000000000000^1593 ≤ 8840426882651^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391160043 10000000000 8840426882651 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656330681/5000000000 : ℝ), (-2065849523/10000000000 : ℝ), (5391160043/10000000000 : ℝ)] ![(2709603730283/6250000000000 : ℝ), (622210294427/5000000000000 : ℝ), (8840426882651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656330681/5000000000 : ℝ)|^2105 ≤ (2709603730283/6250000000000 : ℝ)^1593
        have hw : |(2656330681/5000000000 : ℝ)|=(2656330681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065849523/10000000000 : ℝ)|^2105 ≤ (622210294427/5000000000000 : ℝ)^1593
        have hw : |(-2065849523/10000000000 : ℝ)|=(2065849523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391160043/10000000000 : ℝ)|^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593
        have hw : |(5391160043/10000000000 : ℝ)|=(5391160043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312661361/10000000000 : ℝ)*x 0 + (5391160043/10000000000 : ℝ)*x 1 + (-516462381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312661361/10000000000 : ℝ)^2105 ≤ (8670731934749/20000000000000 : ℝ)^1593 := by
    have hnat : (5312661361 : ℕ)^2105*20000000000000^1593 ≤ 8670731934749^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312661361 10000000000 8670731934749 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391160043/10000000000 : ℝ)^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593 := by
    have hnat : (5391160043 : ℕ)^2105*20000000000000^1593 ≤ 8840426882651^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391160043 10000000000 8840426882651 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516462381/2500000000 : ℝ)^2105 ≤ (24888411793/200000000000 : ℝ)^1593 := by
    have hnat : (516462381 : ℕ)^2105*200000000000^1593 ≤ 24888411793^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516462381 2500000000 24888411793 200000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312661361/10000000000 : ℝ), (5391160043/10000000000 : ℝ), (-516462381/2500000000 : ℝ)] ![(8670731934749/20000000000000 : ℝ), (8840426882651/20000000000000 : ℝ), (24888411793/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312661361/10000000000 : ℝ)|^2105 ≤ (8670731934749/20000000000000 : ℝ)^1593
        have hw : |(5312661361/10000000000 : ℝ)|=(5312661361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391160043/10000000000 : ℝ)|^2105 ≤ (8840426882651/20000000000000 : ℝ)^1593
        have hw : |(5391160043/10000000000 : ℝ)|=(5391160043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516462381/2500000000 : ℝ)|^2105 ≤ (24888411793/200000000000 : ℝ)^1593
        have hw : |(-516462381/2500000000 : ℝ)|=(516462381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352844049/10000000000 : ℝ)*x 0 + (895970031/2000000000 : ℝ)*x 1 + (132167893/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352844049/10000000000 : ℝ)^2105 ≤ (16658755984689/50000000000000 : ℝ)^1593 := by
    have hnat : (4352844049 : ℕ)^2105*50000000000000^1593 ≤ 16658755984689^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352844049 10000000000 16658755984689 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895970031/2000000000 : ℝ)^2105 ≤ (34608073720627/100000000000000 : ℝ)^1593 := by
    have hnat : (895970031 : ℕ)^2105*100000000000000^1593 ≤ 34608073720627^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895970031 2000000000 34608073720627 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132167893/312500000 : ℝ)^2105 ≤ (8018603572813/25000000000000 : ℝ)^1593 := by
    have hnat : (132167893 : ℕ)^2105*25000000000000^1593 ≤ 8018603572813^1593*312500000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132167893 312500000 8018603572813 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352844049/10000000000 : ℝ), (895970031/2000000000 : ℝ), (132167893/312500000 : ℝ)] ![(16658755984689/50000000000000 : ℝ), (34608073720627/100000000000000 : ℝ), (8018603572813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352844049/10000000000 : ℝ)|^2105 ≤ (16658755984689/50000000000000 : ℝ)^1593
        have hw : |(4352844049/10000000000 : ℝ)|=(4352844049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895970031/2000000000 : ℝ)|^2105 ≤ (34608073720627/100000000000000 : ℝ)^1593
        have hw : |(895970031/2000000000 : ℝ)|=(895970031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132167893/312500000 : ℝ)|^2105 ≤ (8018603572813/25000000000000 : ℝ)^1593
        have hw : |(132167893/312500000 : ℝ)|=(132167893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s7_8 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-61901547/10000000000 : ℝ)*x 0 + (5912776969/10000000000 : ℝ)*x 1 + (2956402197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61901547/10000000000 : ℝ)^2105 ≤ (120764915121/100000000000000 : ℝ)^1593 := by
    have hnat : (61901547 : ℕ)^2105*100000000000000^1593 ≤ 120764915121^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61901547 10000000000 120764915121 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5912776969/10000000000 : ℝ)^2105 ≤ (12484866123789/25000000000000 : ℝ)^1593 := by
    have hnat : (5912776969 : ℕ)^2105*25000000000000^1593 ≤ 12484866123789^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912776969 10000000000 12484866123789 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956402197/5000000000 : ℝ)^2105 ≤ (2496988528783/5000000000000 : ℝ)^1593 := by
    have hnat : (2956402197 : ℕ)^2105*5000000000000^1593 ≤ 2496988528783^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956402197 5000000000 2496988528783 5000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61901547/10000000000 : ℝ), (5912776969/10000000000 : ℝ), (2956402197/5000000000 : ℝ)] ![(120764915121/100000000000000 : ℝ), (12484866123789/25000000000000 : ℝ), (2496988528783/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61901547/10000000000 : ℝ)|^2105 ≤ (120764915121/100000000000000 : ℝ)^1593
        have hw : |(-61901547/10000000000 : ℝ)|=(61901547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5912776969/10000000000 : ℝ)|^2105 ≤ (12484866123789/25000000000000 : ℝ)^1593
        have hw : |(5912776969/10000000000 : ℝ)|=(5912776969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956402197/5000000000 : ℝ)|^2105 ≤ (2496988528783/5000000000000 : ℝ)^1593
        have hw : |(2956402197/5000000000 : ℝ)|=(2956402197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (573/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (358/3125 : ℝ) ^ (8419/2048 : ℝ) ≤ (6773379195529941/50000000000000000000 : ℝ) := by
    have hpowers : (358/3125 : ℝ)^8419 ≤ (6773379195529941/50000000000000000000 : ℝ)^2048 := by
      have hnat : (358 : ℕ)^8419*50000000000000000000^2048 ≤ 6773379195529941^2048*3125^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        358 3125 6773379195529941 50000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (358/3125 : ℝ)) (X := (6773379195529941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (8419/2048 : ℝ) ≤ (15910090423975753/50000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^8419 ≤ (15910090423975753/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14101 : ℕ)^8419*50000000000000000000^2048 ≤ 15910090423975753^2048*100000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 15910090423975753 50000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (15910090423975753/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006773379195529941/25000000000000000000 : ℝ) ≤ (10000659007424081/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (25006773379195529941/25000000000000000000 : ℝ)^2048 ≤ (10000659007424081/10000000000000000 : ℝ)^8419 := by
      have hnat : (25006773379195529941 : ℕ)^2048*10000000000000000^8419 ≤ 10000659007424081^8419*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006773379195529941 25000000000000000000 10000659007424081 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000659007424081/10000000000000000 : ℝ)) (X := (25006773379195529941/25000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011341734809752847/25000000000000000000 : ℝ) ≤ (2000220680715217/2000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (25011341734809752847/25000000000000000000 : ℝ)^2048 ≤ (2000220680715217/2000000000000000 : ℝ)^8419 := by
      have hnat : (25011341734809752847 : ℕ)^2048*2000000000000000^8419 ≤ 2000220680715217^8419*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011341734809752847 25000000000000000000 2000220680715217 2000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000220680715217/2000000000000000 : ℝ)) (X := (25011341734809752847/25000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015910090423975753/25000000000000000000 : ℝ) ≤ (10001547799728089/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (25015910090423975753/25000000000000000000 : ℝ)^2048 ≤ (10001547799728089/10000000000000000 : ℝ)^8419 := by
      have hnat : (25015910090423975753 : ℕ)^2048*10000000000000000^8419 ≤ 10001547799728089^8419*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015910090423975753 25000000000000000000 10001547799728089 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001547799728089/10000000000000000 : ℝ)) (X := (25015910090423975753/25000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6773379195529941/50000000000000000000 : ℝ) ≤ ((26441561070001978597/26450000000000000000 : ℝ)+2*(111099038001/66125000000000 : ℝ)*(358/3125 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (26441561070001978597/26450000000000000000 : ℝ)+2*(111099038001/66125000000000 : ℝ)*(358/3125 : ℝ)=(10000659007424081/10000000000000000 : ℝ) by norm_num, show 1+2*(6773379195529941/50000000000000000000 : ℝ)=(25006773379195529941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15910090423975753/50000000000000000000 : ℝ)+(6773379195529941/50000000000000000000 : ℝ) ≤ ((26441561070001978597/26450000000000000000 : ℝ)+(111099038001/66125000000000 : ℝ)*((14101/100000 : ℝ)+(358/3125 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (26441561070001978597/26450000000000000000 : ℝ)+(111099038001/66125000000000 : ℝ)*((14101/100000 : ℝ)+(358/3125 : ℝ))=(2000220680715217/2000000000000000 : ℝ) by norm_num, show 1+(15910090423975753/50000000000000000000 : ℝ)+(6773379195529941/50000000000000000000 : ℝ)=(25011341734809752847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15910090423975753/50000000000000000000 : ℝ) ≤ ((26441561070001978597/26450000000000000000 : ℝ)+2*(111099038001/66125000000000 : ℝ)*(14101/100000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (26441561070001978597/26450000000000000000 : ℝ)+2*(111099038001/66125000000000 : ℝ)*(14101/100000 : ℝ)=(10001547799728089/10000000000000000 : ℝ) by norm_num, show 1+2*(15910090423975753/50000000000000000000 : ℝ)=(25015910090423975753/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26441561070001978597/26450000000000000000 : ℝ)*(X 1 0+X 2 0)+(111099038001/66125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (26441561070001978597/26450000000000000000 : ℝ)) (alpha := (111099038001/66125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26441561070001978597/26450000000000000000 : ℝ)*(X 0 1+X 2 1)+(111099038001/66125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (26441561070001978597/26450000000000000000 : ℝ)) (alpha := (111099038001/66125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26441561070001978597/26450000000000000000 : ℝ)*(X 0 2+X 1 2)+(111099038001/66125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (26441561070001978597/26450000000000000000 : ℝ)) (alpha := (111099038001/66125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531721887/2500000000 : ℝ)*X 0 0+(5391477021/10000000000 : ℝ)*X 0 1+(2633505459/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068876951/2000000000 : ℝ)*X 1 0+(-34218681/156250000 : ℝ)*X 1 1+(5267015029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344388251/10000000000 : ℝ)*X 2 0+(2633506179/5000000000 : ℝ)*X 2 1+(-547498617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352839943/10000000000 : ℝ)*X 0 0+(528591507/1250000000 : ℝ)*X 0 1+(4480482977/10000000000 : ℝ)*X 0 2+(4352839943/10000000000 : ℝ)*X 1 0+(528591507/1250000000 : ℝ)*X 1 1+(4480482977/10000000000 : ℝ)*X 1 2+(4352839943/10000000000 : ℝ)*X 2 0+(528591507/1250000000 : ℝ)*X 2 1+(4480482977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063446261/5000000000 : ℝ)*X 0 0+(2633663281/5000000000 : ℝ)*X 0 1+(5391160043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656330681/5000000000 : ℝ)*X 1 0+(-2065849523/10000000000 : ℝ)*X 1 1+(5391160043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312661361/10000000000 : ℝ)*X 2 0+(5391160043/10000000000 : ℝ)*X 2 1+(-516462381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352844049/10000000000 : ℝ)*X 0 0+(895970031/2000000000 : ℝ)*X 0 1+(132167893/312500000 : ℝ)*X 0 2+(4352844049/10000000000 : ℝ)*X 1 0+(895970031/2000000000 : ℝ)*X 1 1+(132167893/312500000 : ℝ)*X 1 2+(4352844049/10000000000 : ℝ)*X 2 0+(895970031/2000000000 : ℝ)*X 2 1+(132167893/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-61901547/10000000000 : ℝ)*X 0 0+(5912776969/10000000000 : ℝ)*X 0 1+(2956402197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7574402828877821821407863421/1322500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454431683/10000000000000 : ℝ)*(lower2) + (1760399351/100000000000000 : ℝ)*(lower4) + (415073803/50000000000000 : ℝ)*(lower5) + (6003389929562931/100000000000000 : ℝ)*(major0) + (6003389929562931/100000000000000 : ℝ)*(major1) + (6003389929562931/100000000000000 : ℝ)*(major2) + (2008596271447583/25000000000000 : ℝ)*(sp0) + (8034571798072251/100000000000000 : ℝ)*(sp1) + (8034563928147449/100000000000000 : ℝ)*(sp2) + (993039406131097/25000000000000 : ℝ)*(sp3) + (83914882567/50000000000000 : ℝ)*(sp4) + (7869924803/100000000000000 : ℝ)*(sp6) + (12561404497/25000000000000 : ℝ)*(sp7) + (3776503357/20000000000000 : ℝ)*(sp8) + (3972207870142377/100000000000000 : ℝ)*(f.failure) + (8034571798072251/100000000000000 : ℝ)*(f.sum) + (71905937363899/13225000000000000000000000000 : ℝ)*base65 + (24282419420586012193/2645000000000000000000000000000000 : ℝ)*base68 + (47017697175958987807/2645000000000000000000000000000000 : ℝ)*base69 + (42518562328846012193/2645000000000000000000000000000000 : ℝ)*base72 + (66040133057/413281250000000000000000000 : ℝ)*base73 + (9373495061936012193/2645000000000000000000000000000000 : ℝ)*base76 + (2785195842488987807/2645000000000000000000000000000000 : ℝ)*base77 + (27011652952856012193/2645000000000000000000000000000000 : ℝ)*base80 + (6406918490653/1653125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (42414963/5000000000000000000000 : ℝ)*base89 + (42414963/5000000000000000000000 : ℝ)*base91 + (42414963/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1663350113585078219336862501/132250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (646138973/100000000000000 : ℝ)*(lower2) + (6697417/3125000000000 : ℝ)*(lower3) + (64694651/10000000000000 : ℝ)*(lower4) + (215333843/100000000000000 : ℝ)*(lower5) + (603388234446811/10000000000000 : ℝ)*(major0) + (603388234446811/10000000000000 : ℝ)*(major1) + (603388234446811/10000000000000 : ℝ)*(major2) + (1810748323/25000000000000 : ℝ)*(sp0) + (2541660347/50000000000000 : ℝ)*(sp3) + (1615073537635933/20000000000000 : ℝ)*(sp4) + (8075380763469809/100000000000000 : ℝ)*(sp5) + (8075380763469809/100000000000000 : ℝ)*(sp6) + (499047302862727/12500000000000 : ℝ)*(sp7) + (1458074213/25000000000000 : ℝ)*(sp8) + (399238350622251/10000000000000 : ℝ)*(f.failure) + (8075380763469809/100000000000000 : ℝ)*(f.sum) + (64835880311067/661250000000000000000000000 : ℝ)*base65 + (47783294668304167/264500000000000000000000000000000 : ℝ)*base67 + (267523388232804167/264500000000000000000000000000000 : ℝ)*base69 + (3957576835936695833/264500000000000000000000000000000 : ℝ)*base72 + (25873565573377/2645000000000000000000000000 : ℝ)*base74 + (3271959127263195833/264500000000000000000000000000000 : ℝ)*base76 + (1110639071456195833/264500000000000000000000000000000 : ℝ)*base78 + (4047453101968195833/264500000000000000000000000000000 : ℝ)*base80 + (588608090761/1322500000000000000000000000 : ℝ)*base82 + (2040169/500000000000000000000 : ℝ)*base89 + (2040169/500000000000000000000 : ℝ)*base91 + (2040169/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1227_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1227_s8_0 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-132930657/625000000 : ℝ)*x 0 + (5391437359/10000000000 : ℝ)*x 1 + (1053409733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132930657/625000000 : ℝ)^2105 ≤ (808273428007/6250000000000 : ℝ)^1593 := by
    have hnat : (132930657 : ℕ)^2105*6250000000000^1593 ≤ 808273428007^1593*625000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132930657 625000000 808273428007 6250000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391437359/10000000000 : ℝ)^2105 ≤ (44205138938503/100000000000000 : ℝ)^1593 := by
    have hnat : (5391437359 : ℕ)^2105*100000000000000^1593 ≤ 44205138938503^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391437359 10000000000 44205138938503 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053409733/2000000000 : ℝ)^2105 ≤ (8572497241101/20000000000000 : ℝ)^1593 := by
    have hnat : (1053409733 : ℕ)^2105*20000000000000^1593 ≤ 8572497241101^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053409733 2000000000 8572497241101 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132930657/625000000 : ℝ), (5391437359/10000000000 : ℝ), (1053409733/2000000000 : ℝ)] ![(808273428007/6250000000000 : ℝ), (44205138938503/100000000000000 : ℝ), (8572497241101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132930657/625000000 : ℝ)|^2105 ≤ (808273428007/6250000000000 : ℝ)^1593
        have hw : |(-132930657/625000000 : ℝ)|=(132930657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391437359/10000000000 : ℝ)|^2105 ≤ (44205138938503/100000000000000 : ℝ)^1593
        have hw : |(5391437359/10000000000 : ℝ)|=(5391437359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053409733/2000000000 : ℝ)|^2105 ≤ (8572497241101/20000000000000 : ℝ)^1593
        have hw : |(1053409733/2000000000 : ℝ)|=(1053409733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_1 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336094187/2500000000 : ℝ)*x 0 + (-2189961651/10000000000 : ℝ)*x 1 + (5267048667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336094187/2500000000 : ℝ)^2105 ≤ (43695982496269/100000000000000 : ℝ)^1593 := by
    have hnat : (1336094187 : ℕ)^2105*100000000000000^1593 ≤ 43695982496269^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336094187 2500000000 43695982496269 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189961651/10000000000 : ℝ)^2105 ≤ (6720765632533/50000000000000 : ℝ)^1593 := by
    have hnat : (2189961651 : ℕ)^2105*50000000000000^1593 ≤ 6720765632533^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189961651 10000000000 6720765632533 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267048667/10000000000 : ℝ)^2105 ≤ (10715621556753/25000000000000 : ℝ)^1593 := by
    have hnat : (5267048667 : ℕ)^2105*25000000000000^1593 ≤ 10715621556753^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267048667 10000000000 10715621556753 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336094187/2500000000 : ℝ), (-2189961651/10000000000 : ℝ), (5267048667/10000000000 : ℝ)] ![(43695982496269/100000000000000 : ℝ), (6720765632533/50000000000000 : ℝ), (10715621556753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336094187/2500000000 : ℝ)|^2105 ≤ (43695982496269/100000000000000 : ℝ)^1593
        have hw : |(1336094187/2500000000 : ℝ)|=(1336094187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189961651/10000000000 : ℝ)|^2105 ≤ (6720765632533/50000000000000 : ℝ)^1593
        have hw : |(-2189961651/10000000000 : ℝ)|=(2189961651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267048667/10000000000 : ℝ)|^2105 ≤ (10715621556753/25000000000000 : ℝ)^1593
        have hw : |(5267048667/10000000000 : ℝ)|=(5267048667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_2 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534437673/1000000000 : ℝ)*x 0 + (5267048663/10000000000 : ℝ)*x 1 + (-27374521/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534437673/1000000000 : ℝ)^2105 ≤ (43695982301799/100000000000000 : ℝ)^1593 := by
    have hnat : (534437673 : ℕ)^2105*100000000000000^1593 ≤ 43695982301799^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534437673 1000000000 43695982301799 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267048663/10000000000 : ℝ)^2105 ≤ (42862486183999/100000000000000 : ℝ)^1593 := by
    have hnat : (5267048663 : ℕ)^2105*100000000000000^1593 ≤ 42862486183999^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267048663 10000000000 42862486183999 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27374521/125000000 : ℝ)^2105 ≤ (13441531500271/100000000000000 : ℝ)^1593 := by
    have hnat : (27374521 : ℕ)^2105*100000000000000^1593 ≤ 13441531500271^1593*125000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27374521 125000000 13441531500271 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534437673/1000000000 : ℝ), (5267048663/10000000000 : ℝ), (-27374521/125000000 : ℝ)] ![(43695982301799/100000000000000 : ℝ), (42862486183999/100000000000000 : ℝ), (13441531500271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534437673/1000000000 : ℝ)|^2105 ≤ (43695982301799/100000000000000 : ℝ)^1593
        have hw : |(534437673/1000000000 : ℝ)|=(534437673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267048663/10000000000 : ℝ)|^2105 ≤ (42862486183999/100000000000000 : ℝ)^1593
        have hw : |(5267048663/10000000000 : ℝ)|=(5267048663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27374521/125000000 : ℝ)|^2105 ≤ (13441531500271/100000000000000 : ℝ)^1593
        have hw : |(-27374521/125000000 : ℝ)|=(27374521/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_3 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (544104543/1250000000 : ℝ)*x 0 + (528601217/1250000000 : ℝ)*x 1 + (2240205147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544104543/1250000000 : ℝ)^2105 ≤ (4164679254841/12500000000000 : ℝ)^1593 := by
    have hnat : (544104543 : ℕ)^2105*12500000000000^1593 ≤ 4164679254841^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544104543 1250000000 4164679254841 12500000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528601217/1250000000 : ℝ)^2105 ≤ (3206877408767/10000000000000 : ℝ)^1593 := by
    have hnat : (528601217 : ℕ)^2105*10000000000000^1593 ≤ 3206877408767^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528601217 1250000000 3206877408767 10000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240205147/5000000000 : ℝ)^2105 ≤ (34613791860859/100000000000000 : ℝ)^1593 := by
    have hnat : (2240205147 : ℕ)^2105*100000000000000^1593 ≤ 34613791860859^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240205147 5000000000 34613791860859 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544104543/1250000000 : ℝ), (528601217/1250000000 : ℝ), (2240205147/5000000000 : ℝ)] ![(4164679254841/12500000000000 : ℝ), (3206877408767/10000000000000 : ℝ), (34613791860859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544104543/1250000000 : ℝ)|^2105 ≤ (4164679254841/12500000000000 : ℝ)^1593
        have hw : |(544104543/1250000000 : ℝ)|=(544104543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528601217/1250000000 : ℝ)|^2105 ≤ (3206877408767/10000000000000 : ℝ)^1593
        have hw : |(528601217/1250000000 : ℝ)|=(528601217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240205147/5000000000 : ℝ)|^2105 ≤ (34613791860859/100000000000000 : ℝ)^1593
        have hw : |(2240205147/5000000000 : ℝ)|=(2240205147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_4 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063447861/5000000000 : ℝ)*x 0 + (1053472321/2000000000 : ℝ)*x 1 + (673890361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063447861/5000000000 : ℝ)^2105 ≤ (12932416708897/100000000000000 : ℝ)^1593 := by
    have hnat : (1063447861 : ℕ)^2105*100000000000000^1593 ≤ 12932416708897^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063447861 5000000000 12932416708897 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053472321/2000000000 : ℝ)^2105 ≤ (42865851410901/100000000000000 : ℝ)^1593 := by
    have hnat : (1053472321 : ℕ)^2105*100000000000000^1593 ≤ 42865851410901^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053472321 2000000000 42865851410901 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673890361/1250000000 : ℝ)^2105 ≤ (44201731868543/100000000000000 : ℝ)^1593 := by
    have hnat : (673890361 : ℕ)^2105*100000000000000^1593 ≤ 44201731868543^1593*1250000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673890361 1250000000 44201731868543 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063447861/5000000000 : ℝ), (1053472321/2000000000 : ℝ), (673890361/1250000000 : ℝ)] ![(12932416708897/100000000000000 : ℝ), (42865851410901/100000000000000 : ℝ), (44201731868543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063447861/5000000000 : ℝ)|^2105 ≤ (12932416708897/100000000000000 : ℝ)^1593
        have hw : |(-1063447861/5000000000 : ℝ)|=(1063447861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053472321/2000000000 : ℝ)|^2105 ≤ (42865851410901/100000000000000 : ℝ)^1593
        have hw : |(1053472321/2000000000 : ℝ)|=(1053472321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673890361/1250000000 : ℝ)|^2105 ≤ (44201731868543/100000000000000 : ℝ)^1593
        have hw : |(673890361/1250000000 : ℝ)|=(673890361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_5 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312671487/10000000000 : ℝ)*x 0 + (-2065886939/10000000000 : ℝ)*x 1 + (215644899/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312671487/10000000000 : ℝ)^2105 ≤ (21676884432519/50000000000000 : ℝ)^1593 := by
    have hnat : (5312671487 : ℕ)^2105*50000000000000^1593 ≤ 21676884432519^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312671487 10000000000 21676884432519 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065886939/10000000000 : ℝ)^2105 ≤ (12444503715117/100000000000000 : ℝ)^1593 := by
    have hnat : (2065886939 : ℕ)^2105*100000000000000^1593 ≤ 12444503715117^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065886939 10000000000 12444503715117 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215644899/400000000 : ℝ)^2105 ≤ (44201727394023/100000000000000 : ℝ)^1593 := by
    have hnat : (215644899 : ℕ)^2105*100000000000000^1593 ≤ 44201727394023^1593*400000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215644899 400000000 44201727394023 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312671487/10000000000 : ℝ), (-2065886939/10000000000 : ℝ), (215644899/400000000 : ℝ)] ![(21676884432519/50000000000000 : ℝ), (12444503715117/100000000000000 : ℝ), (44201727394023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312671487/10000000000 : ℝ)|^2105 ≤ (21676884432519/50000000000000 : ℝ)^1593
        have hw : |(5312671487/10000000000 : ℝ)|=(5312671487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065886939/10000000000 : ℝ)|^2105 ≤ (12444503715117/100000000000000 : ℝ)^1593
        have hw : |(-2065886939/10000000000 : ℝ)|=(2065886939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215644899/400000000 : ℝ)|^2105 ≤ (44201727394023/100000000000000 : ℝ)^1593
        have hw : |(215644899/400000000 : ℝ)|=(215644899/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_6 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26563357/50000000 : ℝ)*x 0 + (5391122309/10000000000 : ℝ)*x 1 + (-516471821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26563357/50000000 : ℝ)^2105 ≤ (21676883963447/50000000000000 : ℝ)^1593 := by
    have hnat : (26563357 : ℕ)^2105*50000000000000^1593 ≤ 21676883963447^1593*50000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26563357 50000000 21676883963447 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391122309/10000000000 : ℝ)^2105 ≤ (11050431398887/25000000000000 : ℝ)^1593 := by
    have hnat : (5391122309 : ℕ)^2105*25000000000000^1593 ≤ 11050431398887^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391122309 10000000000 11050431398887 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516471821/2500000000 : ℝ)^2105 ≤ (12444506461281/100000000000000 : ℝ)^1593 := by
    have hnat : (516471821 : ℕ)^2105*100000000000000^1593 ≤ 12444506461281^1593*2500000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516471821 2500000000 12444506461281 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26563357/50000000 : ℝ), (5391122309/10000000000 : ℝ), (-516471821/2500000000 : ℝ)] ![(21676883963447/50000000000000 : ℝ), (11050431398887/25000000000000 : ℝ), (12444506461281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26563357/50000000 : ℝ)|^2105 ≤ (21676883963447/50000000000000 : ℝ)^1593
        have hw : |(26563357/50000000 : ℝ)|=(26563357/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391122309/10000000000 : ℝ)|^2105 ≤ (11050431398887/25000000000000 : ℝ)^1593
        have hw : |(5391122309/10000000000 : ℝ)|=(5391122309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516471821/2500000000 : ℝ)|^2105 ≤ (12444506461281/100000000000000 : ℝ)^1593
        have hw : |(-516471821/2500000000 : ℝ)|=(516471821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_7 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (435284593/1000000000 : ℝ)*x 0 + (2239888207/5000000000 : ℝ)*x 1 + (845889159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435284593/1000000000 : ℝ)^2105 ≤ (53308049591/160000000000 : ℝ)^1593 := by
    have hnat : (435284593 : ℕ)^2105*160000000000^1593 ≤ 53308049591^1593*1000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435284593 1000000000 53308049591 160000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239888207/5000000000 : ℝ)^2105 ≤ (34607320957847/100000000000000 : ℝ)^1593 := by
    have hnat : (2239888207 : ℕ)^2105*100000000000000^1593 ≤ 34607320957847^1593*5000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239888207 5000000000 34607320957847 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845889159/2000000000 : ℝ)^2105 ≤ (6415029606899/20000000000000 : ℝ)^1593 := by
    have hnat : (845889159 : ℕ)^2105*20000000000000^1593 ≤ 6415029606899^1593*2000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845889159 2000000000 6415029606899 20000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435284593/1000000000 : ℝ), (2239888207/5000000000 : ℝ), (845889159/2000000000 : ℝ)] ![(53308049591/160000000000 : ℝ), (34607320957847/100000000000000 : ℝ), (6415029606899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435284593/1000000000 : ℝ)|^2105 ≤ (53308049591/160000000000 : ℝ)^1593
        have hw : |(435284593/1000000000 : ℝ)|=(435284593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239888207/5000000000 : ℝ)|^2105 ≤ (34607320957847/100000000000000 : ℝ)^1593
        have hw : |(2239888207/5000000000 : ℝ)|=(2239888207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845889159/2000000000 : ℝ)|^2105 ≤ (6415029606899/20000000000000 : ℝ)^1593
        have hw : |(845889159/2000000000 : ℝ)|=(845889159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1227_s8_8 (p : ℝ) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-37195133/10000000000 : ℝ)*x 0 + (5811068569/10000000000 : ℝ)*x 1 + (376201529/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37195133/10000000000 : ℝ)^2105 ≤ (15401584969/25000000000000 : ℝ)^1593 := by
    have hnat : (37195133 : ℕ)^2105*25000000000000^1593 ≤ 15401584969^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37195133 10000000000 15401584969 25000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5811068569/10000000000 : ℝ)^2105 ≤ (24403742425467/50000000000000 : ℝ)^1593 := by
    have hnat : (5811068569 : ℕ)^2105*50000000000000^1593 ≤ 24403742425467^1593*10000000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5811068569 10000000000 24403742425467 50000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376201529/625000000 : ℝ)^2105 ≤ (51130908802819/100000000000000 : ℝ)^1593 := by
    have hnat : (376201529 : ℕ)^2105*100000000000000^1593 ≤ 51130908802819^1593*625000000^2105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376201529 625000000 51130908802819 100000000000000 2105 1593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2105/512 : ℝ)) 2105 1593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37195133/10000000000 : ℝ), (5811068569/10000000000 : ℝ), (376201529/625000000 : ℝ)] ![(15401584969/25000000000000 : ℝ), (24403742425467/50000000000000 : ℝ), (51130908802819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37195133/10000000000 : ℝ)|^2105 ≤ (15401584969/25000000000000 : ℝ)^1593
        have hw : |(-37195133/10000000000 : ℝ)|=(37195133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5811068569/10000000000 : ℝ)|^2105 ≤ (24403742425467/50000000000000 : ℝ)^1593
        have hw : |(5811068569/10000000000 : ℝ)|=(5811068569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376201529/625000000 : ℝ)|^2105 ≤ (51130908802819/100000000000000 : ℝ)^1593
        have hw : |(376201529/625000000 : ℝ)|=(376201529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1227_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11461/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (573/5000 : ℝ) ^ (8419/2048 : ℝ) ≤ (3391553320327211/25000000000000000000 : ℝ) := by
    have hpowers : (573/5000 : ℝ)^8419 ≤ (3391553320327211/25000000000000000000 : ℝ)^2048 := by
      have hnat : (573 : ℕ)^8419*25000000000000000000^2048 ≤ 3391553320327211^2048*5000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 5000 3391553320327211 25000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/5000 : ℝ)) (X := (3391553320327211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (8419/2048 : ℝ) ≤ (31783091290193481/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^8419 ≤ (31783091290193481/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14097 : ℕ)^8419*100000000000000000000^2048 ≤ 31783091290193481^2048*100000^8419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 31783091290193481 100000000000000000000 8419 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (31783091290193481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503391553320327211/12500000000000000000 : ℝ) ≤ (10000659953746501/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (12503391553320327211/12500000000000000000 : ℝ)^2048 ≤ (10000659953746501/10000000000000000 : ℝ)^8419 := by
      have hnat : (12503391553320327211 : ℕ)^2048*10000000000000000^8419 ≤ 10000659953746501^8419*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503391553320327211 12500000000000000000 10000659953746501 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000659953746501/10000000000000000 : ℝ)) (X := (12503391553320327211/12500000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001813972182860093/4000000000000000000 : ℝ) ≤ (10001102974743593/10000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (4001813972182860093/4000000000000000000 : ℝ)^2048 ≤ (10001102974743593/10000000000000000 : ℝ)^8419 := by
      have hnat : (4001813972182860093 : ℕ)^2048*10000000000000000^8419 ≤ 10001102974743593^8419*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001813972182860093 4000000000000000000 10001102974743593 10000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001102974743593/10000000000000000 : ℝ)) (X := (4001813972182860093/4000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031783091290193481/50000000000000000000 : ℝ) ≤ (2000309199148137/2000000000000000 : ℝ) ^ (8419/2048 : ℝ) := by
    have hpowers : (50031783091290193481/50000000000000000000 : ℝ)^2048 ≤ (2000309199148137/2000000000000000 : ℝ)^8419 := by
      have hnat : (50031783091290193481 : ℕ)^2048*2000000000000000^8419 ≤ 2000309199148137^8419*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031783091290193481 50000000000000000000 2000309199148137 2000000000000000 2048 8419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000309199148137/2000000000000000 : ℝ)) (X := (50031783091290193481/50000000000000000000 : ℝ)) (by norm_num) 8419 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3391553320327211/25000000000000000000 : ℝ) ≤ ((8787195418925391499/8790000000000000000 : ℝ)+2*(110755249273/65925000000000 : ℝ)*(573/5000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (8787195418925391499/8790000000000000000 : ℝ)+2*(110755249273/65925000000000 : ℝ)*(573/5000 : ℝ)=(10000659953746501/10000000000000000 : ℝ) by norm_num, show 1+2*(3391553320327211/25000000000000000000 : ℝ)=(12503391553320327211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31783091290193481/100000000000000000000 : ℝ)+(3391553320327211/25000000000000000000 : ℝ) ≤ ((8787195418925391499/8790000000000000000 : ℝ)+(110755249273/65925000000000 : ℝ)*((14097/100000 : ℝ)+(573/5000 : ℝ)))^(8419/2048 : ℝ) := by
    rw [show (8787195418925391499/8790000000000000000 : ℝ)+(110755249273/65925000000000 : ℝ)*((14097/100000 : ℝ)+(573/5000 : ℝ))=(10001102974743593/10000000000000000 : ℝ) by norm_num, show 1+(31783091290193481/100000000000000000000 : ℝ)+(3391553320327211/25000000000000000000 : ℝ)=(4001813972182860093/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31783091290193481/100000000000000000000 : ℝ) ≤ ((8787195418925391499/8790000000000000000 : ℝ)+2*(110755249273/65925000000000 : ℝ)*(14097/100000 : ℝ))^(8419/2048 : ℝ) := by
    rw [show (8787195418925391499/8790000000000000000 : ℝ)+2*(110755249273/65925000000000 : ℝ)*(14097/100000 : ℝ)=(2000309199148137/2000000000000000 : ℝ) by norm_num, show 1+2*(31783091290193481/100000000000000000000 : ℝ)=(50031783091290193481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8787195418925391499/8790000000000000000 : ℝ)*(X 1 0+X 2 0)+(110755249273/65925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (8787195418925391499/8790000000000000000 : ℝ)) (alpha := (110755249273/65925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8787195418925391499/8790000000000000000 : ℝ)*(X 0 1+X 2 1)+(110755249273/65925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (8787195418925391499/8790000000000000000 : ℝ)) (alpha := (110755249273/65925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8787195418925391499/8790000000000000000 : ℝ)*(X 0 2+X 1 2)+(110755249273/65925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8419/2048 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (8787195418925391499/8790000000000000000 : ℝ)) (alpha := (110755249273/65925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132930657/625000000 : ℝ)*X 0 0+(5391437359/10000000000 : ℝ)*X 0 1+(1053409733/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336094187/2500000000 : ℝ)*X 1 0+(-2189961651/10000000000 : ℝ)*X 1 1+(5267048667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534437673/1000000000 : ℝ)*X 2 0+(5267048663/10000000000 : ℝ)*X 2 1+(-27374521/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544104543/1250000000 : ℝ)*X 0 0+(528601217/1250000000 : ℝ)*X 0 1+(2240205147/5000000000 : ℝ)*X 0 2+(544104543/1250000000 : ℝ)*X 1 0+(528601217/1250000000 : ℝ)*X 1 1+(2240205147/5000000000 : ℝ)*X 1 2+(544104543/1250000000 : ℝ)*X 2 0+(528601217/1250000000 : ℝ)*X 2 1+(2240205147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063447861/5000000000 : ℝ)*X 0 0+(1053472321/2000000000 : ℝ)*X 0 1+(673890361/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312671487/10000000000 : ℝ)*X 1 0+(-2065886939/10000000000 : ℝ)*X 1 1+(215644899/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26563357/50000000 : ℝ)*X 2 0+(5391122309/10000000000 : ℝ)*X 2 1+(-516471821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435284593/1000000000 : ℝ)*X 0 0+(2239888207/5000000000 : ℝ)*X 0 1+(845889159/2000000000 : ℝ)*X 0 2+(435284593/1000000000 : ℝ)*X 1 0+(2239888207/5000000000 : ℝ)*X 1 1+(845889159/2000000000 : ℝ)*X 1 2+(435284593/1000000000 : ℝ)*X 2 0+(2239888207/5000000000 : ℝ)*X 2 1+(845889159/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-37195133/10000000000 : ℝ)*X 0 0+(5811068569/10000000000 : ℝ)*X 0 1+(376201529/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1227_s8_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17615744857447920436263231/2289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (370882293/100000000000000 : ℝ)*(lower2) + (48663751/25000000000000 : ℝ)*(lower3) + (199945859/50000000000000 : ℝ)*(lower4) + (12482043/12500000000000 : ℝ)*(lower5) + (93858428144019/1562500000000 : ℝ)*(major0) + (93858428144019/1562500000000 : ℝ)*(major1) + (93858428144019/1562500000000 : ℝ)*(major2) + (8039318546398059/100000000000000 : ℝ)*(sp0) + (803931622597777/10000000000000 : ℝ)*(sp1) + (4019655820219239/50000000000000 : ℝ)*(sp2) + (3974556416447951/100000000000000 : ℝ)*(sp3) + (5903488171/100000000000000 : ℝ)*(sp5) + (10489027463/100000000000000 : ℝ)*(sp6) + (3583067883/100000000000000 : ℝ)*(sp8) + (3974556416447951/100000000000000 : ℝ)*(f.failure) + (8039322129465941/100000000000000 : ℝ)*(f.sum) + (560819354800691/4395000000000000000000000000 : ℝ)*base66 + (294034791005855519/13734375000000000000000000000000 : ℝ)*base68 + (82520990232326197/6867187500000000000000000000000 : ℝ)*base70 + (167478525436736303/6867187500000000000000000000000 : ℝ)*base71 + (2360109022309/4395000000000000000000000000 : ℝ)*base73 + (7559079599294947/6867187500000000000000000000000 : ℝ)*base76 + (227168262565081981/13734375000000000000000000000000 : ℝ)*base77 + (92795946572201197/6867187500000000000000000000000 : ℝ)*base80 + (10888719463067/2197500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4908469/5000000000000000000000 : ℝ)*base89 + (4908469/5000000000000000000000 : ℝ)*base91 + (4908469/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14269334644109446756487/2197500000000000000000000000 : ℝ) := by norm_num
    linear_combination (101198119/50000000000000 : ℝ)*(upper1) + (1080867747/100000000000000 : ℝ)*(lower2) + (407205523/100000000000000 : ℝ)*(lower3) + (1151164921/100000000000000 : ℝ)*(lower4) + (882641333/100000000000000 : ℝ)*(lower5) + (3018716642288599/50000000000000 : ℝ)*(major0) + (3018716642288599/50000000000000 : ℝ)*(major1) + (3018716642288599/50000000000000 : ℝ)*(major2) + (20363309457/50000000000000 : ℝ)*(sp0) + (8080080164388153/100000000000000 : ℝ)*(sp4) + (323205333142371/4000000000000 : ℝ)*(sp5) + (323205333142371/4000000000000 : ℝ)*(sp6) + (798946604829417/20000000000000 : ℝ)*(sp7) + (6218776103/50000000000000 : ℝ)*(sp8) + (798946604829417/20000000000000 : ℝ)*(f.failure) + (323205333142371/4000000000000 : ℝ)*(f.sum) + (605243701620557/6592500000000000000000000000 : ℝ)*base66 + (13984339286410959703/1318500000000000000000000000000000 : ℝ)*base67 + (12326566516642040297/1318500000000000000000000000000000 : ℝ)*base70 + (11269329073630959703/1318500000000000000000000000000000 : ℝ)*base71 + (66314127829691/13185000000000000000000000000 : ℝ)*base73 + (26946150377531540297/1318500000000000000000000000000000 : ℝ)*base76 + (173868300770756540297/1318500000000000000000000000000000 : ℝ)*base78 + (13228207132615959703/1318500000000000000000000000000000 : ℝ)*base79 + (67475007615341/13185000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base84 + (2035277/1000000000000000000000 : ℝ)*base90 + (2035277/1000000000000000000000 : ℝ)*base92 + (2035277/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1227_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1227_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1227_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1227_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1227_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1227_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8419/2048 : ℝ) ≤ p) (hpb : p ≤ (2105/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75567419/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1227_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
