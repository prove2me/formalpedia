-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:24.781373+00:00
-- url     : https://prove2.me/submissions/293cee90-25fe-4e03-8147-dfe9d2e20fb0

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
theorem support_rectangle_w1279_s3_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048568381/5000000000 : ℝ)*x 0 + (5436052947/10000000000 : ℝ)*x 1 + (1044804871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048568381/5000000000 : ℝ)^4239 ≤ (12751466277683/100000000000000 : ℝ)^3215 := by
    have hnat : (1048568381 : ℕ)^4239*100000000000000^3215 ≤ 12751466277683^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048568381 5000000000 12751466277683 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436052947/10000000000 : ℝ)^4239 ≤ (44768204531537/100000000000000 : ℝ)^3215 := by
    have hnat : (5436052947 : ℕ)^4239*100000000000000^3215 ≤ 44768204531537^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436052947 10000000000 44768204531537 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044804871/2000000000 : ℝ)^4239 ≤ (21240164590727/50000000000000 : ℝ)^3215 := by
    have hnat : (1044804871 : ℕ)^4239*50000000000000^3215 ≤ 21240164590727^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044804871 2000000000 21240164590727 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048568381/5000000000 : ℝ), (5436052947/10000000000 : ℝ), (1044804871/2000000000 : ℝ)] ![(12751466277683/100000000000000 : ℝ), (44768204531537/100000000000000 : ℝ), (21240164590727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048568381/5000000000 : ℝ)|^4239 ≤ (12751466277683/100000000000000 : ℝ)^3215
        have hw : |(-1048568381/5000000000 : ℝ)|=(1048568381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436052947/10000000000 : ℝ)|^4239 ≤ (44768204531537/100000000000000 : ℝ)^3215
        have hw : |(5436052947/10000000000 : ℝ)|=(5436052947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044804871/2000000000 : ℝ)|^4239 ≤ (21240164590727/50000000000000 : ℝ)^3215
        have hw : |(1044804871/2000000000 : ℝ)|=(1044804871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355056129/10000000000 : ℝ)*x 0 + (-441138861/2000000000 : ℝ)*x 1 + (5224024481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355056129/10000000000 : ℝ)^4239 ≤ (43890797460283/100000000000000 : ℝ)^3215 := by
    have hnat : (5355056129 : ℕ)^4239*100000000000000^3215 ≤ 43890797460283^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355056129 10000000000 43890797460283 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441138861/2000000000 : ℝ)^4239 ≤ (6814435999649/50000000000000 : ℝ)^3215 := by
    have hnat : (441138861 : ℕ)^4239*50000000000000^3215 ≤ 6814435999649^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441138861 2000000000 6814435999649 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224024481/10000000000 : ℝ)^4239 ≤ (42480330532393/100000000000000 : ℝ)^3215 := by
    have hnat : (5224024481 : ℕ)^4239*100000000000000^3215 ≤ 42480330532393^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224024481 10000000000 42480330532393 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355056129/10000000000 : ℝ), (-441138861/2000000000 : ℝ), (5224024481/10000000000 : ℝ)] ![(43890797460283/100000000000000 : ℝ), (6814435999649/50000000000000 : ℝ), (42480330532393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355056129/10000000000 : ℝ)|^4239 ≤ (43890797460283/100000000000000 : ℝ)^3215
        have hw : |(5355056129/10000000000 : ℝ)|=(5355056129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441138861/2000000000 : ℝ)|^4239 ≤ (6814435999649/50000000000000 : ℝ)^3215
        have hw : |(-441138861/2000000000 : ℝ)|=(441138861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224024481/10000000000 : ℝ)|^4239 ≤ (42480330532393/100000000000000 : ℝ)^3215
        have hw : |(5224024481/10000000000 : ℝ)|=(5224024481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669382021/1250000000 : ℝ)*x 0 + (2612012099/5000000000 : ℝ)*x 1 + (-17645557/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669382021/1250000000 : ℝ)^4239 ≤ (43890797881743/100000000000000 : ℝ)^3215 := by
    have hnat : (669382021 : ℕ)^4239*100000000000000^3215 ≤ 43890797881743^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669382021 1250000000 43890797881743 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612012099/5000000000 : ℝ)^4239 ≤ (21240163749071/50000000000000 : ℝ)^3215 := by
    have hnat : (2612012099 : ℕ)^4239*50000000000000^3215 ≤ 21240163749071^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612012099 5000000000 21240163749071 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17645557/80000000 : ℝ)^4239 ≤ (6814437303167/50000000000000 : ℝ)^3215 := by
    have hnat : (17645557 : ℕ)^4239*50000000000000^3215 ≤ 6814437303167^3215*80000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17645557 80000000 6814437303167 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669382021/1250000000 : ℝ), (2612012099/5000000000 : ℝ), (-17645557/80000000 : ℝ)] ![(43890797881743/100000000000000 : ℝ), (21240163749071/50000000000000 : ℝ), (6814437303167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669382021/1250000000 : ℝ)|^4239 ≤ (43890797881743/100000000000000 : ℝ)^3215
        have hw : |(669382021/1250000000 : ℝ)|=(669382021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612012099/5000000000 : ℝ)|^4239 ≤ (21240163749071/50000000000000 : ℝ)^3215
        have hw : |(2612012099/5000000000 : ℝ)|=(2612012099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17645557/80000000 : ℝ)|^4239 ≤ (6814437303167/50000000000000 : ℝ)^3215
        have hw : |(-17645557/80000000 : ℝ)|=(17645557/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170919851/5000000000 : ℝ)*x 0 + (4130237249/10000000000 : ℝ)*x 1 + (912768617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170919851/5000000000 : ℝ)^4239 ≤ (8321667500331/25000000000000 : ℝ)^3215 := by
    have hnat : (2170919851 : ℕ)^4239*25000000000000^3215 ≤ 8321667500331^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170919851 5000000000 8321667500331 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130237249/10000000000 : ℝ)^4239 ≤ (31164513292397/100000000000000 : ℝ)^3215 := by
    have hnat : (4130237249 : ℕ)^4239*100000000000000^3215 ≤ 31164513292397^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130237249 10000000000 31164513292397 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912768617/2000000000 : ℝ)^4239 ≤ (1421952667863/4000000000000 : ℝ)^3215 := by
    have hnat : (912768617 : ℕ)^4239*4000000000000^3215 ≤ 1421952667863^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912768617 2000000000 1421952667863 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170919851/5000000000 : ℝ), (4130237249/10000000000 : ℝ), (912768617/2000000000 : ℝ)] ![(8321667500331/25000000000000 : ℝ), (31164513292397/100000000000000 : ℝ), (1421952667863/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170919851/5000000000 : ℝ)|^4239 ≤ (8321667500331/25000000000000 : ℝ)^3215
        have hw : |(2170919851/5000000000 : ℝ)|=(2170919851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130237249/10000000000 : ℝ)|^4239 ≤ (31164513292397/100000000000000 : ℝ)^3215
        have hw : |(4130237249/10000000000 : ℝ)|=(4130237249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(912768617/2000000000 : ℝ)|^4239 ≤ (1421952667863/4000000000000 : ℝ)^3215
        have hw : |(912768617/2000000000 : ℝ)|=(912768617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2097160313/10000000000 : ℝ)*x 0 + (5224946189/10000000000 : ℝ)*x 1 + (33969533/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097160313/10000000000 : ℝ)^4239 ≤ (2550331017619/20000000000000 : ℝ)^3215 := by
    have hnat : (2097160313 : ℕ)^4239*20000000000000^3215 ≤ 2550331017619^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097160313 10000000000 2550331017619 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224946189/10000000000 : ℝ)^4239 ≤ (10622553280053/25000000000000 : ℝ)^3215 := by
    have hnat : (5224946189 : ℕ)^4239*25000000000000^3215 ≤ 10622553280053^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224946189 10000000000 10622553280053 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33969533/62500000 : ℝ)^4239 ≤ (8951626353119/20000000000000 : ℝ)^3215 := by
    have hnat : (33969533 : ℕ)^4239*20000000000000^3215 ≤ 8951626353119^3215*62500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33969533 62500000 8951626353119 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2097160313/10000000000 : ℝ), (5224946189/10000000000 : ℝ), (33969533/62500000 : ℝ)] ![(2550331017619/20000000000000 : ℝ), (10622553280053/25000000000000 : ℝ), (8951626353119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2097160313/10000000000 : ℝ)|^4239 ≤ (2550331017619/20000000000000 : ℝ)^3215
        have hw : |(-2097160313/10000000000 : ℝ)|=(2097160313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224946189/10000000000 : ℝ)|^4239 ≤ (10622553280053/25000000000000 : ℝ)^3215
        have hw : |(5224946189/10000000000 : ℝ)|=(5224946189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33969533/62500000 : ℝ)|^4239 ≤ (8951626353119/20000000000000 : ℝ)^3215
        have hw : |(33969533/62500000 : ℝ)|=(33969533/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5300856573/10000000000 : ℝ)*x 0 + (-1994593269/10000000000 : ℝ)*x 1 + (1358781303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5300856573/10000000000 : ℝ)^4239 ≤ (10826506752833/25000000000000 : ℝ)^3215 := by
    have hnat : (5300856573 : ℕ)^4239*25000000000000^3215 ≤ 10826506752833^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5300856573 10000000000 10826506752833 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1994593269/10000000000 : ℝ)^4239 ≤ (2387168389961/20000000000000 : ℝ)^3215 := by
    have hnat : (1994593269 : ℕ)^4239*20000000000000^3215 ≤ 2387168389961^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994593269 10000000000 2387168389961 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358781303/2500000000 : ℝ)^4239 ≤ (44758131027259/100000000000000 : ℝ)^3215 := by
    have hnat : (1358781303 : ℕ)^4239*100000000000000^3215 ≤ 44758131027259^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358781303 2500000000 44758131027259 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5300856573/10000000000 : ℝ), (-1994593269/10000000000 : ℝ), (1358781303/2500000000 : ℝ)] ![(10826506752833/25000000000000 : ℝ), (2387168389961/20000000000000 : ℝ), (44758131027259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5300856573/10000000000 : ℝ)|^4239 ≤ (10826506752833/25000000000000 : ℝ)^3215
        have hw : |(5300856573/10000000000 : ℝ)|=(5300856573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1994593269/10000000000 : ℝ)|^4239 ≤ (2387168389961/20000000000000 : ℝ)^3215
        have hw : |(-1994593269/10000000000 : ℝ)|=(1994593269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358781303/2500000000 : ℝ)|^4239 ≤ (44758131027259/100000000000000 : ℝ)^3215
        have hw : |(1358781303/2500000000 : ℝ)|=(1358781303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265042829/500000000 : ℝ)*x 0 + (5435125193/10000000000 : ℝ)*x 1 + (-997296643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265042829/500000000 : ℝ)^4239 ≤ (21653013543367/50000000000000 : ℝ)^3215 := by
    have hnat : (265042829 : ℕ)^4239*50000000000000^3215 ≤ 21653013543367^3215*500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265042829 500000000 21653013543367 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435125193/10000000000 : ℝ)^4239 ≤ (279738317631/625000000000 : ℝ)^3215 := by
    have hnat : (5435125193 : ℕ)^4239*625000000000^3215 ≤ 279738317631^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435125193 10000000000 279738317631 625000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997296643/5000000000 : ℝ)^4239 ≤ (372995065123/3125000000000 : ℝ)^3215 := by
    have hnat : (997296643 : ℕ)^4239*3125000000000^3215 ≤ 372995065123^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997296643 5000000000 372995065123 3125000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265042829/500000000 : ℝ), (5435125193/10000000000 : ℝ), (-997296643/5000000000 : ℝ)] ![(21653013543367/50000000000000 : ℝ), (279738317631/625000000000 : ℝ), (372995065123/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265042829/500000000 : ℝ)|^4239 ≤ (21653013543367/50000000000000 : ℝ)^3215
        have hw : |(265042829/500000000 : ℝ)|=(265042829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435125193/10000000000 : ℝ)|^4239 ≤ (279738317631/625000000000 : ℝ)^3215
        have hw : |(5435125193/10000000000 : ℝ)|=(5435125193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997296643/5000000000 : ℝ)|^4239 ≤ (372995065123/3125000000000 : ℝ)^3215
        have hw : |(-997296643/5000000000 : ℝ)|=(997296643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s3_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341887493/10000000000 : ℝ)*x 0 + (912391539/2000000000 : ℝ)*x 1 + (2066067363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341887493/10000000000 : ℝ)^4239 ≤ (33287153088917/100000000000000 : ℝ)^3215 := by
    have hnat : (4341887493 : ℕ)^4239*100000000000000^3215 ≤ 33287153088917^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341887493 10000000000 33287153088917 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912391539/2000000000 : ℝ)^4239 ≤ (17764727364069/50000000000000 : ℝ)^3215 := by
    have hnat : (912391539 : ℕ)^4239*50000000000000^3215 ≤ 17764727364069^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912391539 2000000000 17764727364069 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066067363/5000000000 : ℝ)^4239 ≤ (3118339216601/10000000000000 : ℝ)^3215 := by
    have hnat : (2066067363 : ℕ)^4239*10000000000000^3215 ≤ 3118339216601^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066067363 5000000000 3118339216601 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341887493/10000000000 : ℝ), (912391539/2000000000 : ℝ), (2066067363/5000000000 : ℝ)] ![(33287153088917/100000000000000 : ℝ), (17764727364069/50000000000000 : ℝ), (3118339216601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341887493/10000000000 : ℝ)|^4239 ≤ (33287153088917/100000000000000 : ℝ)^3215
        have hw : |(4341887493/10000000000 : ℝ)|=(4341887493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(912391539/2000000000 : ℝ)|^4239 ≤ (17764727364069/50000000000000 : ℝ)^3215
        have hw : |(912391539/2000000000 : ℝ)|=(912391539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066067363/5000000000 : ℝ)|^4239 ≤ (3118339216601/10000000000000 : ℝ)^3215
        have hw : |(2066067363/5000000000 : ℝ)|=(2066067363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10599/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3771/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (294/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8189/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (294/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (294/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8189/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (294/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (294/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8189/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (294/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (294/3125 : ℝ) ^ (2119/512 : ℝ) ≤ (141117927842293/2500000000000000000 : ℝ) := by
    have hpowers : (294/3125 : ℝ)^2119 ≤ (141117927842293/2500000000000000000 : ℝ)^512 := by
      have hnat : (294 : ℕ)^2119*2500000000000000000^512 ≤ 141117927842293^512*3125^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        294 3125 141117927842293 2500000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (294/3125 : ℝ)) (X := (141117927842293/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8189/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (55986529631067513/100000000000000000000 : ℝ) := by
    have hpowers : (8189/50000 : ℝ)^2119 ≤ (55986529631067513/100000000000000000000 : ℝ)^512 := by
      have hnat : (8189 : ℕ)^2119*100000000000000000000^512 ≤ 55986529631067513^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8189 50000 55986529631067513 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8189/50000 : ℝ)) (X := (55986529631067513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250141117927842293/1250000000000000000 : ℝ) ≤ (10000272767479999/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (1250141117927842293/1250000000000000000 : ℝ)^512 ≤ (10000272767479999/10000000000000000 : ℝ)^2119 := by
      have hnat : (1250141117927842293 : ℕ)^512*10000000000000000^2119 ≤ 10000272767479999^2119*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250141117927842293 1250000000000000000 10000272767479999 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272767479999/10000000000000000 : ℝ)) (X := (1250141117927842293/1250000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061631246744759233/100000000000000000000 : ℝ) ≤ (10001488807295629/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (100061631246744759233/100000000000000000000 : ℝ)^512 ≤ (10001488807295629/10000000000000000 : ℝ)^2119 := by
      have hnat : (100061631246744759233 : ℕ)^512*10000000000000000^2119 ≤ 10001488807295629^2119*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061631246744759233 100000000000000000000 10001488807295629 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001488807295629/10000000000000000 : ℝ)) (X := (100061631246744759233/100000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055986529631067513/50000000000000000000 : ℝ) ≤ (10002704847111259/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50055986529631067513/50000000000000000000 : ℝ)^512 ≤ (10002704847111259/10000000000000000 : ℝ)^2119 := by
      have hnat : (50055986529631067513 : ℕ)^512*10000000000000000^2119 ≤ 10002704847111259^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055986529631067513 50000000000000000000 10002704847111259 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002704847111259/10000000000000000 : ℝ)) (X := (50055986529631067513/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141117927842293/2500000000000000000 : ℝ) ≤ ((1393580403683293979/1394000000000000000 : ℝ)+2*(121603981563/69700000000000 : ℝ)*(294/3125 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1393580403683293979/1394000000000000000 : ℝ)+2*(121603981563/69700000000000 : ℝ)*(294/3125 : ℝ)=(10000272767479999/10000000000000000 : ℝ) by norm_num, show 1+2*(141117927842293/2500000000000000000 : ℝ)=(1250141117927842293/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55986529631067513/100000000000000000000 : ℝ)+(141117927842293/2500000000000000000 : ℝ) ≤ ((1393580403683293979/1394000000000000000 : ℝ)+(121603981563/69700000000000 : ℝ)*((8189/50000 : ℝ)+(294/3125 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1393580403683293979/1394000000000000000 : ℝ)+(121603981563/69700000000000 : ℝ)*((8189/50000 : ℝ)+(294/3125 : ℝ))=(10001488807295629/10000000000000000 : ℝ) by norm_num, show 1+(55986529631067513/100000000000000000000 : ℝ)+(141117927842293/2500000000000000000 : ℝ)=(100061631246744759233/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55986529631067513/100000000000000000000 : ℝ) ≤ ((1393580403683293979/1394000000000000000 : ℝ)+2*(121603981563/69700000000000 : ℝ)*(8189/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1393580403683293979/1394000000000000000 : ℝ)+2*(121603981563/69700000000000 : ℝ)*(8189/50000 : ℝ)=(10002704847111259/10000000000000000 : ℝ) by norm_num, show 1+2*(55986529631067513/100000000000000000000 : ℝ)=(50055986529631067513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1393580403683293979/1394000000000000000 : ℝ)*(X 1 0+X 2 0)+(121603981563/69700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (294/3125 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (1393580403683293979/1394000000000000000 : ℝ)) (alpha := (121603981563/69700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1393580403683293979/1394000000000000000 : ℝ)*(X 0 1+X 2 1)+(121603981563/69700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (294/3125 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (1393580403683293979/1394000000000000000 : ℝ)) (alpha := (121603981563/69700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1393580403683293979/1394000000000000000 : ℝ)*(X 0 2+X 1 2)+(121603981563/69700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (294/3125 : ℝ)) (hi := (8189/50000 : ℝ)) (c := (1393580403683293979/1394000000000000000 : ℝ)) (alpha := (121603981563/69700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048568381/5000000000 : ℝ)*X 0 0+(5436052947/10000000000 : ℝ)*X 0 1+(1044804871/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355056129/10000000000 : ℝ)*X 1 0+(-441138861/2000000000 : ℝ)*X 1 1+(5224024481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669382021/1250000000 : ℝ)*X 2 0+(2612012099/5000000000 : ℝ)*X 2 1+(-17645557/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170919851/5000000000 : ℝ)*X 0 0+(4130237249/10000000000 : ℝ)*X 0 1+(912768617/2000000000 : ℝ)*X 0 2+(2170919851/5000000000 : ℝ)*X 1 0+(4130237249/10000000000 : ℝ)*X 1 1+(912768617/2000000000 : ℝ)*X 1 2+(2170919851/5000000000 : ℝ)*X 2 0+(4130237249/10000000000 : ℝ)*X 2 1+(912768617/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2097160313/10000000000 : ℝ)*X 0 0+(5224946189/10000000000 : ℝ)*X 0 1+(33969533/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5300856573/10000000000 : ℝ)*X 1 0+(-1994593269/10000000000 : ℝ)*X 1 1+(1358781303/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265042829/500000000 : ℝ)*X 2 0+(5435125193/10000000000 : ℝ)*X 2 1+(-997296643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341887493/10000000000 : ℝ)*X 0 0+(912391539/2000000000 : ℝ)*X 0 1+(2066067363/5000000000 : ℝ)*X 0 2+(4341887493/10000000000 : ℝ)*X 1 0+(912391539/2000000000 : ℝ)*X 1 1+(2066067363/5000000000 : ℝ)*X 1 2+(4341887493/10000000000 : ℝ)*X 2 0+(912391539/2000000000 : ℝ)*X 2 1+(2066067363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2435406701408552963031/348500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1172239013/100000000000000 : ℝ)*(base19) + (1124415281/100000000000000 : ℝ)*(base23) + (80499011/100000000000000 : ℝ)*(lower2) + (375076689/100000000000000 : ℝ)*(upper3) + (36495263/100000000000000 : ℝ)*(lower4) + (175565982192531/5000000000000 : ℝ)*(major0) + (175565982192531/5000000000000 : ℝ)*(major1) + (175565982192531/5000000000000 : ℝ)*(major2) + (294772927088499/6250000000000 : ℝ)*(sp0) + (2358188614745089/50000000000000 : ℝ)*(sp1) + (471637727731391/10000000000000 : ℝ)*(sp2) + (2306248822833403/100000000000000 : ℝ)*(sp3) + (1446039151/12500000000000 : ℝ)*(sp4) + (11830196821/100000000000000 : ℝ)*(sp7) + (144141290814389/6250000000000 : ℝ)*(f.failure) + (4716378401729191/100000000000000 : ℝ)*(f.sum) + (6325193724153/697000000000000000000000000 : ℝ)*base65 + (6275486609190849/6970000000000000000000000000000 : ℝ)*base67 + (8282597371039151/6970000000000000000000000000000 : ℝ)*base70 + (19313279221760849/6970000000000000000000000000000 : ℝ)*base71 + (9526154787/10890625000000000000000000 : ℝ)*base73 + (40506990994700849/6970000000000000000000000000000 : ℝ)*base75 + (1411987326699151/6970000000000000000000000000000 : ℝ)*base78 + (29159470780209151/6970000000000000000000000000000 : ℝ)*base80 + (110328211953/139400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4966429/625000000000000000000 : ℝ)*base90 + (4966429/625000000000000000000 : ℝ)*base92 + (4966429/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (419075170900072986508664589/69700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1476225613/100000000000000 : ℝ)*(base19) + (762605497/50000000000000 : ℝ)*(base23) + (67531077/50000000000000 : ℝ)*(upper3) + (971891/4000000000000 : ℝ)*(lower4) + (20718213/12500000000000 : ℝ)*(upper5) + (3542193313919197/100000000000000 : ℝ)*(major0) + (3542193313919197/100000000000000 : ℝ)*(major1) + (3542193313919197/100000000000000 : ℝ)*(major2) + (23991531813/100000000000000 : ℝ)*(sp1) + (2368499893/10000000000000 : ℝ)*(sp2) + (2378923860031833/50000000000000 : ℝ)*(sp4) + (4757822252306239/100000000000000 : ℝ)*(sp5) + (2378911254926871/50000000000000 : ℝ)*(sp6) + (116326935367809/5000000000000 : ℝ)*(sp7) + (116326935367809/5000000000000 : ℝ)*(f.failure) + (2378923860031833/50000000000000 : ℝ)*(f.sum) + (14572113817141/3485000000000000000000000000 : ℝ)*base65 + (105053921474765137/139400000000000000000000000000000 : ℝ)*base68 + (1008910862003165137/139400000000000000000000000000000 : ℝ)*base70 + (924446640079234863/139400000000000000000000000000000 : ℝ)*base71 + (4213798066429/3485000000000000000000000000 : ℝ)*base74 + (629034225401434863/139400000000000000000000000000000 : ℝ)*base75 + (688694589495165137/139400000000000000000000000000000 : ℝ)*base78 + (1960406790671565137/139400000000000000000000000000000 : ℝ)*base80 + (8052540809819/3485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3088951/500000000000000000000 : ℝ)*base89 + (3088951/500000000000000000000 : ℝ)*base91 + (3088951/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1279_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3771/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s4_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099199343/10000000000 : ℝ)*x 0 + (5419949633/10000000000 : ℝ)*x 1 + (5238776181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099199343/10000000000 : ℝ)^4239 ≤ (12768004728583/100000000000000 : ℝ)^3215 := by
    have hnat : (2099199343 : ℕ)^4239*100000000000000^3215 ≤ 12768004728583^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099199343 10000000000 12768004728583 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419949633/10000000000 : ℝ)^4239 ≤ (44593429805281/100000000000000 : ℝ)^3215 := by
    have hnat : (5419949633 : ℕ)^4239*100000000000000^3215 ≤ 44593429805281^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419949633 10000000000 44593429805281 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238776181/10000000000 : ℝ)^4239 ≤ (42638565451507/100000000000000 : ℝ)^3215 := by
    have hnat : (5238776181 : ℕ)^4239*100000000000000^3215 ≤ 42638565451507^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238776181 10000000000 42638565451507 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099199343/10000000000 : ℝ), (5419949633/10000000000 : ℝ), (5238776181/10000000000 : ℝ)] ![(12768004728583/100000000000000 : ℝ), (44593429805281/100000000000000 : ℝ), (42638565451507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099199343/10000000000 : ℝ)|^4239 ≤ (12768004728583/100000000000000 : ℝ)^3215
        have hw : |(-2099199343/10000000000 : ℝ)|=(2099199343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419949633/10000000000 : ℝ)|^4239 ≤ (44593429805281/100000000000000 : ℝ)^3215
        have hw : |(5419949633/10000000000 : ℝ)|=(5419949633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238776181/10000000000 : ℝ)|^4239 ≤ (42638565451507/100000000000000 : ℝ)^3215
        have hw : |(5238776181/10000000000 : ℝ)|=(5238776181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350995041/10000000000 : ℝ)*x 0 + (-547910939/2500000000 : ℝ)*x 1 + (5238776177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350995041/10000000000 : ℝ)^4239 ≤ (2192345796213/5000000000000 : ℝ)^3215 := by
    have hnat : (5350995041 : ℕ)^4239*5000000000000^3215 ≤ 2192345796213^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350995041 10000000000 2192345796213 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547910939/2500000000 : ℝ)^4239 ≤ (3378629662839/25000000000000 : ℝ)^3215 := by
    have hnat : (547910939 : ℕ)^4239*25000000000000^3215 ≤ 3378629662839^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547910939 2500000000 3378629662839 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238776177/10000000000 : ℝ)^4239 ≤ (42638565408581/100000000000000 : ℝ)^3215 := by
    have hnat : (5238776177 : ℕ)^4239*100000000000000^3215 ≤ 42638565408581^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238776177 10000000000 42638565408581 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350995041/10000000000 : ℝ), (-547910939/2500000000 : ℝ), (5238776177/10000000000 : ℝ)] ![(2192345796213/5000000000000 : ℝ), (3378629662839/25000000000000 : ℝ), (42638565408581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350995041/10000000000 : ℝ)|^4239 ≤ (2192345796213/5000000000000 : ℝ)^3215
        have hw : |(5350995041/10000000000 : ℝ)|=(5350995041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547910939/2500000000 : ℝ)|^4239 ≤ (3378629662839/25000000000000 : ℝ)^3215
        have hw : |(-547910939/2500000000 : ℝ)|=(547910939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238776177/10000000000 : ℝ)|^4239 ≤ (42638565408581/100000000000000 : ℝ)^3215
        have hw : |(5238776177/10000000000 : ℝ)|=(5238776177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350994859/10000000000 : ℝ)*x 0 + (2619388167/5000000000 : ℝ)*x 1 + (-219164379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350994859/10000000000 : ℝ)^4239 ≤ (43846913957921/100000000000000 : ℝ)^3215 := by
    have hnat : (5350994859 : ℕ)^4239*100000000000000^3215 ≤ 43846913957921^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350994859 10000000000 43846913957921 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619388167/5000000000 : ℝ)^4239 ≤ (42638567093407/100000000000000 : ℝ)^3215 := by
    have hnat : (2619388167 : ℕ)^4239*100000000000000^3215 ≤ 42638567093407^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619388167 5000000000 42638567093407 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219164379/1000000000 : ℝ)^4239 ≤ (1351451892779/10000000000000 : ℝ)^3215 := by
    have hnat : (219164379 : ℕ)^4239*10000000000000^3215 ≤ 1351451892779^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219164379 1000000000 1351451892779 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350994859/10000000000 : ℝ), (2619388167/5000000000 : ℝ), (-219164379/1000000000 : ℝ)] ![(43846913957921/100000000000000 : ℝ), (42638567093407/100000000000000 : ℝ), (1351451892779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350994859/10000000000 : ℝ)|^4239 ≤ (43846913957921/100000000000000 : ℝ)^3215
        have hw : |(5350994859/10000000000 : ℝ)|=(5350994859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619388167/5000000000 : ℝ)|^4239 ≤ (42638567093407/100000000000000 : ℝ)^3215
        have hw : |(2619388167/5000000000 : ℝ)|=(2619388167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219164379/1000000000 : ℝ)|^4239 ≤ (1351451892779/10000000000000 : ℝ)^3215
        have hw : |(-219164379/1000000000 : ℝ)|=(219164379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171542129/5000000000 : ℝ)*x 0 + (4161630281/10000000000 : ℝ)*x 1 + (2266067829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171542129/5000000000 : ℝ)^4239 ≤ (33299250946519/100000000000000 : ℝ)^3215 := by
    have hnat : (2171542129 : ℕ)^4239*100000000000000^3215 ≤ 33299250946519^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171542129 5000000000 33299250946519 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161630281/10000000000 : ℝ)^4239 ≤ (1259088463757/4000000000000 : ℝ)^3215 := by
    have hnat : (4161630281 : ℕ)^4239*4000000000000^3215 ≤ 1259088463757^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161630281 10000000000 1259088463757 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266067829/5000000000 : ℝ)^4239 ≤ (17611768728171/50000000000000 : ℝ)^3215 := by
    have hnat : (2266067829 : ℕ)^4239*50000000000000^3215 ≤ 17611768728171^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266067829 5000000000 17611768728171 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171542129/5000000000 : ℝ), (4161630281/10000000000 : ℝ), (2266067829/5000000000 : ℝ)] ![(33299250946519/100000000000000 : ℝ), (1259088463757/4000000000000 : ℝ), (17611768728171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171542129/5000000000 : ℝ)|^4239 ≤ (33299250946519/100000000000000 : ℝ)^3215
        have hw : |(2171542129/5000000000 : ℝ)|=(2171542129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161630281/10000000000 : ℝ)|^4239 ≤ (1259088463757/4000000000000 : ℝ)^3215
        have hw : |(4161630281/10000000000 : ℝ)|=(4161630281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266067829/5000000000 : ℝ)|^4239 ≤ (17611768728171/50000000000000 : ℝ)^3215
        have hw : |(2266067829/5000000000 : ℝ)|=(2266067829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099214229/10000000000 : ℝ)*x 0 + (2619724993/5000000000 : ℝ)*x 1 + (2709636027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099214229/10000000000 : ℝ)^4239 ≤ (1596015513529/12500000000000 : ℝ)^3215 := by
    have hnat : (2099214229 : ℕ)^4239*12500000000000^3215 ≤ 1596015513529^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099214229 10000000000 1596015513529 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619724993/5000000000 : ℝ)^4239 ≤ (10661449112639/25000000000000 : ℝ)^3215 := by
    have hnat : (2619724993 : ℕ)^4239*25000000000000^3215 ≤ 10661449112639^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619724993 5000000000 10661449112639 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709636027/5000000000 : ℝ)^4239 ≤ (2229303971633/5000000000000 : ℝ)^3215 := by
    have hnat : (2709636027 : ℕ)^4239*5000000000000^3215 ≤ 2229303971633^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709636027 5000000000 2229303971633 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099214229/10000000000 : ℝ), (2619724993/5000000000 : ℝ), (2709636027/5000000000 : ℝ)] ![(1596015513529/12500000000000 : ℝ), (10661449112639/25000000000000 : ℝ), (2229303971633/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099214229/10000000000 : ℝ)|^4239 ≤ (1596015513529/12500000000000 : ℝ)^3215
        have hw : |(-2099214229/10000000000 : ℝ)|=(2099214229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619724993/5000000000 : ℝ)|^4239 ≤ (10661449112639/25000000000000 : ℝ)^3215
        have hw : |(2619724993/5000000000 : ℝ)|=(2619724993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709636027/5000000000 : ℝ)|^4239 ≤ (2229303971633/5000000000000 : ℝ)^3215
        have hw : |(2709636027/5000000000 : ℝ)|=(2709636027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331542917/625000000 : ℝ)*x 0 + (-2011147829/10000000000 : ℝ)*x 1 + (5419272153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331542917/625000000 : ℝ)^4239 ≤ (2167364424037/5000000000000 : ℝ)^3215 := by
    have hnat : (331542917 : ℕ)^4239*5000000000000^3215 ≤ 2167364424037^3215*625000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331542917 625000000 2167364424037 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011147829/10000000000 : ℝ)^4239 ≤ (754164437169/6250000000000 : ℝ)^3215 := by
    have hnat : (2011147829 : ℕ)^4239*6250000000000^3215 ≤ 754164437169^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011147829 10000000000 754164437169 6250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419272153/10000000000 : ℝ)^4239 ≤ (4458608050659/10000000000000 : ℝ)^3215 := by
    have hnat : (5419272153 : ℕ)^4239*10000000000000^3215 ≤ 4458608050659^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419272153 10000000000 4458608050659 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331542917/625000000 : ℝ), (-2011147829/10000000000 : ℝ), (5419272153/10000000000 : ℝ)] ![(2167364424037/5000000000000 : ℝ), (754164437169/6250000000000 : ℝ), (4458608050659/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331542917/625000000 : ℝ)|^4239 ≤ (2167364424037/5000000000000 : ℝ)^3215
        have hw : |(331542917/625000000 : ℝ)|=(331542917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011147829/10000000000 : ℝ)|^4239 ≤ (754164437169/6250000000000 : ℝ)^3215
        have hw : |(-2011147829/10000000000 : ℝ)|=(2011147829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419272153/10000000000 : ℝ)|^4239 ≤ (4458608050659/10000000000000 : ℝ)^3215
        have hw : |(5419272153/10000000000 : ℝ)|=(5419272153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304686627/10000000000 : ℝ)*x 0 + (169352251/312500000 : ℝ)*x 1 + (-2011148057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304686627/10000000000 : ℝ)^4239 ≤ (43347287995901/100000000000000 : ℝ)^3215 := by
    have hnat : (5304686627 : ℕ)^4239*100000000000000^3215 ≤ 43347287995901^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304686627 10000000000 43347287995901 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169352251/312500000 : ℝ)^4239 ≤ (44586079194009/100000000000000 : ℝ)^3215 := by
    have hnat : (169352251 : ℕ)^4239*100000000000000^3215 ≤ 44586079194009^3215*312500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169352251 312500000 44586079194009 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011148057/10000000000 : ℝ)^4239 ≤ (754164549899/6250000000000 : ℝ)^3215 := by
    have hnat : (2011148057 : ℕ)^4239*6250000000000^3215 ≤ 754164549899^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011148057 10000000000 754164549899 6250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304686627/10000000000 : ℝ), (169352251/312500000 : ℝ), (-2011148057/10000000000 : ℝ)] ![(43347287995901/100000000000000 : ℝ), (44586079194009/100000000000000 : ℝ), (754164549899/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304686627/10000000000 : ℝ)|^4239 ≤ (43347287995901/100000000000000 : ℝ)^3215
        have hw : |(5304686627/10000000000 : ℝ)|=(5304686627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169352251/312500000 : ℝ)|^4239 ≤ (44586079194009/100000000000000 : ℝ)^3215
        have hw : |(169352251/312500000 : ℝ)|=(169352251/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011148057/10000000000 : ℝ)|^4239 ≤ (754164549899/6250000000000 : ℝ)^3215
        have hw : |(-2011148057/10000000000 : ℝ)|=(2011148057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s4_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542889301/1250000000 : ℝ)*x 0 + (566344673/1250000000 : ℝ)*x 1 + (2081507901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542889301/1250000000 : ℝ)^4239 ≤ (33299555740541/100000000000000 : ℝ)^3215 := by
    have hnat : (542889301 : ℕ)^4239*100000000000000^3215 ≤ 33299555740541^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542889301 1250000000 33299555740541 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566344673/1250000000 : ℝ)^4239 ≤ (35209414453831/100000000000000 : ℝ)^3215 := by
    have hnat : (566344673 : ℕ)^4239*100000000000000^3215 ≤ 35209414453831^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566344673 1250000000 35209414453831 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081507901/5000000000 : ℝ)^4239 ≤ (31491029789477/100000000000000 : ℝ)^3215 := by
    have hnat : (2081507901 : ℕ)^4239*100000000000000^3215 ≤ 31491029789477^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081507901 5000000000 31491029789477 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542889301/1250000000 : ℝ), (566344673/1250000000 : ℝ), (2081507901/5000000000 : ℝ)] ![(33299555740541/100000000000000 : ℝ), (35209414453831/100000000000000 : ℝ), (31491029789477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542889301/1250000000 : ℝ)|^4239 ≤ (33299555740541/100000000000000 : ℝ)^3215
        have hw : |(542889301/1250000000 : ℝ)|=(542889301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566344673/1250000000 : ℝ)|^4239 ≤ (35209414453831/100000000000000 : ℝ)^3215
        have hw : |(566344673/1250000000 : ℝ)|=(566344673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081507901/5000000000 : ℝ)|^4239 ≤ (31491029789477/100000000000000 : ℝ)^3215
        have hw : |(2081507901/5000000000 : ℝ)|=(2081507901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3771/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5457/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3771/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3771/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3771/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3771/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3771/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3771/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10599/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (288895811439799/3125000000000000000 : ℝ) := by
    have hpowers : (10599/100000 : ℝ)^2119 ≤ (288895811439799/3125000000000000000 : ℝ)^512 := by
      have hnat : (10599 : ℕ)^2119*3125000000000000000^512 ≤ 288895811439799^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10599 100000 288895811439799 3125000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10599/100000 : ℝ)) (X := (288895811439799/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3771/25000 : ℝ) ^ (2119/512 : ℝ) ≤ (7964883660959839/20000000000000000000 : ℝ) := by
    have hpowers : (3771/25000 : ℝ)^2119 ≤ (7964883660959839/20000000000000000000 : ℝ)^512 := by
      have hnat : (3771 : ℕ)^2119*20000000000000000000^512 ≤ 7964883660959839^512*25000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3771 25000 7964883660959839 20000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3771/25000 : ℝ)) (X := (7964883660959839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562788895811439799/1562500000000000000 : ℝ) ≤ (2000089342844059/2000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (1562788895811439799/1562500000000000000 : ℝ)^512 ≤ (2000089342844059/2000000000000000 : ℝ)^2119 := by
      have hnat : (1562788895811439799 : ℕ)^512*2000000000000000^2119 ≤ 2000089342844059^2119*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562788895811439799 1562500000000000000 2000089342844059 2000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000089342844059/2000000000000000 : ℝ)) (X := (1562788895811439799/1562500000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049069084270872763/100000000000000000000 : ℝ) ≤ (10001185403394531/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (100049069084270872763/100000000000000000000 : ℝ)^512 ≤ (10001185403394531/10000000000000000 : ℝ)^2119 := by
      have hnat : (100049069084270872763 : ℕ)^512*10000000000000000^2119 ≤ 10001185403394531^2119*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049069084270872763 100000000000000000000 10001185403394531 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001185403394531/10000000000000000 : ℝ)) (X := (100049069084270872763/100000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007964883660959839/10000000000000000000 : ℝ) ≤ (10001924092568767/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (10007964883660959839/10000000000000000000 : ℝ)^512 ≤ (10001924092568767/10000000000000000 : ℝ)^2119 := by
      have hnat : (10007964883660959839 : ℕ)^512*10000000000000000^2119 ≤ 10001924092568767^2119*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007964883660959839 10000000000000000000 10001924092568767 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001924092568767/10000000000000000 : ℝ)) (X := (10007964883660959839/10000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(288895811439799/3125000000000000000 : ℝ) ≤ ((1149649866158014573/1150000000000000000 : ℝ)+2*(14205561043/8625000000000 : ℝ)*(10599/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1149649866158014573/1150000000000000000 : ℝ)+2*(14205561043/8625000000000 : ℝ)*(10599/100000 : ℝ)=(2000089342844059/2000000000000000 : ℝ) by norm_num, show 1+2*(288895811439799/3125000000000000000 : ℝ)=(1562788895811439799/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7964883660959839/20000000000000000000 : ℝ)+(288895811439799/3125000000000000000 : ℝ) ≤ ((1149649866158014573/1150000000000000000 : ℝ)+(14205561043/8625000000000 : ℝ)*((3771/25000 : ℝ)+(10599/100000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1149649866158014573/1150000000000000000 : ℝ)+(14205561043/8625000000000 : ℝ)*((3771/25000 : ℝ)+(10599/100000 : ℝ))=(10001185403394531/10000000000000000 : ℝ) by norm_num, show 1+(7964883660959839/20000000000000000000 : ℝ)+(288895811439799/3125000000000000000 : ℝ)=(100049069084270872763/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7964883660959839/20000000000000000000 : ℝ) ≤ ((1149649866158014573/1150000000000000000 : ℝ)+2*(14205561043/8625000000000 : ℝ)*(3771/25000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1149649866158014573/1150000000000000000 : ℝ)+2*(14205561043/8625000000000 : ℝ)*(3771/25000 : ℝ)=(10001924092568767/10000000000000000 : ℝ) by norm_num, show 1+2*(7964883660959839/20000000000000000000 : ℝ)=(10007964883660959839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1149649866158014573/1150000000000000000 : ℝ)*(X 1 0+X 2 0)+(14205561043/8625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (3771/25000 : ℝ)) (c := (1149649866158014573/1150000000000000000 : ℝ)) (alpha := (14205561043/8625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1149649866158014573/1150000000000000000 : ℝ)*(X 0 1+X 2 1)+(14205561043/8625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (3771/25000 : ℝ)) (c := (1149649866158014573/1150000000000000000 : ℝ)) (alpha := (14205561043/8625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1149649866158014573/1150000000000000000 : ℝ)*(X 0 2+X 1 2)+(14205561043/8625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10599/100000 : ℝ)) (hi := (3771/25000 : ℝ)) (c := (1149649866158014573/1150000000000000000 : ℝ)) (alpha := (14205561043/8625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2099199343/10000000000 : ℝ)*X 0 0+(5419949633/10000000000 : ℝ)*X 0 1+(5238776181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350995041/10000000000 : ℝ)*X 1 0+(-547910939/2500000000 : ℝ)*X 1 1+(5238776177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350994859/10000000000 : ℝ)*X 2 0+(2619388167/5000000000 : ℝ)*X 2 1+(-219164379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171542129/5000000000 : ℝ)*X 0 0+(4161630281/10000000000 : ℝ)*X 0 1+(2266067829/5000000000 : ℝ)*X 0 2+(2171542129/5000000000 : ℝ)*X 1 0+(4161630281/10000000000 : ℝ)*X 1 1+(2266067829/5000000000 : ℝ)*X 1 2+(2171542129/5000000000 : ℝ)*X 2 0+(4161630281/10000000000 : ℝ)*X 2 1+(2266067829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2099214229/10000000000 : ℝ)*X 0 0+(2619724993/5000000000 : ℝ)*X 0 1+(2709636027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331542917/625000000 : ℝ)*X 1 0+(-2011147829/10000000000 : ℝ)*X 1 1+(5419272153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304686627/10000000000 : ℝ)*X 2 0+(169352251/312500000 : ℝ)*X 2 1+(-2011148057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542889301/1250000000 : ℝ)*X 0 0+(566344673/1250000000 : ℝ)*X 0 1+(2081507901/5000000000 : ℝ)*X 0 2+(542889301/1250000000 : ℝ)*X 1 0+(566344673/1250000000 : ℝ)*X 1 1+(2081507901/5000000000 : ℝ)*X 1 2+(542889301/1250000000 : ℝ)*X 2 0+(566344673/1250000000 : ℝ)*X 2 1+(2081507901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (283722726018133404807761827/28750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1282830397/100000000000000 : ℝ)*(base19) + (445487377/50000000000000 : ℝ)*(base23) + (148940663/100000000000000 : ℝ)*(lower2) + (227264573/100000000000000 : ℝ)*(upper3) + (19857999/50000000000000 : ℝ)*(lower4) + (4109330149888933/100000000000000 : ℝ)*(major0) + (4109330149888933/100000000000000 : ℝ)*(major1) + (4109330149888933/100000000000000 : ℝ)*(major2) + (2759800239379201/50000000000000 : ℝ)*(sp0) + (5519620321720921/100000000000000 : ℝ)*(sp1) + (1103924142715313/20000000000000 : ℝ)*(sp2) + (16868909754977/625000000000 : ℝ)*(sp3) + (21125792917/100000000000000 : ℝ)*(sp4) + (12805476331/100000000000000 : ℝ)*(sp7) + (53980767325453/2000000000000 : ℝ)*(f.failure) + (2759810802275659/50000000000000 : ℝ)*(f.sum) + (11971014934049/1725000000000000000000000000 : ℝ)*base66 + (5026541813856138173/345000000000000000000000000000000 : ℝ)*base68 + (5139137963106138173/345000000000000000000000000000000 : ℝ)*base70 + (4105702561221138173/345000000000000000000000000000000 : ℝ)*base72 + (74360486591/26953125000000000000000000 : ℝ)*base74 + (1701845947371138173/345000000000000000000000000000000 : ℝ)*base76 + (47777770748861827/345000000000000000000000000000000 : ℝ)*base77 + (9438711307146138173/345000000000000000000000000000000 : ℝ)*base80 + (2504543346431/431250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (332533/200000000000000000000 : ℝ)*base90 + (332533/200000000000000000000 : ℝ)*base92 + (332533/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29150734032318833340774043/3593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075596611/100000000000000 : ℝ)*(base19) + (230644223/20000000000000 : ℝ)*(base23) + (4111281/4000000000000 : ℝ)*(upper3) + (9775171/10000000000000 : ℝ)*(lower4) + (211911241/100000000000000 : ℝ)*(upper5) + (258761006116703/6250000000000 : ℝ)*(major0) + (258761006116703/6250000000000 : ℝ)*(major1) + (258761006116703/6250000000000 : ℝ)*(major2) + (24652845449/100000000000000 : ℝ)*(sp1) + (17839959859/100000000000000 : ℝ)*(sp2) + (1112210742565143/20000000000000 : ℝ)*(sp4) + (1112205596876731/20000000000000 : ℝ)*(sp5) + (5561034719644741/100000000000000 : ℝ)*(sp6) + (84978069141411/3125000000000 : ℝ)*(sp7) + (84978069141411/3125000000000 : ℝ)*(f.failure) + (1112210742565143/20000000000000 : ℝ)*(f.sum) + (6029150218931/1725000000000000000000000000 : ℝ)*base65 + (88538075410363457/21562500000000000000000000000000 : ℝ)*base67 + (205014212046613457/21562500000000000000000000000000 : ℝ)*base69 + (110354102390675957/21562500000000000000000000000000 : ℝ)*base71 + (4078124076131/1725000000000000000000000000 : ℝ)*base73 + (123207124322761543/21562500000000000000000000000000 : ℝ)*base76 + (129816869449738457/21562500000000000000000000000000 : ℝ)*base77 + (218494041255886543/21562500000000000000000000000000 : ℝ)*base80 + (6562318780331/1725000000000000000000000000 : ℝ)*base81 + (2477371/312500000000000000000 : ℝ)*base90 + (2477371/312500000000000000000 : ℝ)*base92 + (2477371/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3771/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s5_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419918597/2000000000 : ℝ)*x 0 + (2708316831/5000000000 : ℝ)*x 1 + (1048366693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419918597/2000000000 : ℝ)^4239 ≤ (12771161667587/100000000000000 : ℝ)^3215 := by
    have hnat : (419918597 : ℕ)^4239*100000000000000^3215 ≤ 12771161667587^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419918597 2000000000 12771161667587 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708316831/5000000000 : ℝ)^4239 ≤ (348105163769/781250000000 : ℝ)^3215 := by
    have hnat : (2708316831 : ℕ)^4239*781250000000^3215 ≤ 348105163769^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708316831 5000000000 348105163769 781250000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048366693/2000000000 : ℝ)^4239 ≤ (21335688673461/50000000000000 : ℝ)^3215 := by
    have hnat : (1048366693 : ℕ)^4239*50000000000000^3215 ≤ 21335688673461^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048366693 2000000000 21335688673461 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419918597/2000000000 : ℝ), (2708316831/5000000000 : ℝ), (1048366693/2000000000 : ℝ)] ![(12771161667587/100000000000000 : ℝ), (348105163769/781250000000 : ℝ), (21335688673461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419918597/2000000000 : ℝ)|^4239 ≤ (12771161667587/100000000000000 : ℝ)^3215
        have hw : |(-419918597/2000000000 : ℝ)|=(419918597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708316831/5000000000 : ℝ)|^4239 ≤ (348105163769/781250000000 : ℝ)^3215
        have hw : |(2708316831/5000000000 : ℝ)|=(2708316831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048366693/2000000000 : ℝ)|^4239 ≤ (21335688673461/50000000000000 : ℝ)^3215
        have hw : |(1048366693/2000000000 : ℝ)|=(1048366693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350156009/10000000000 : ℝ)*x 0 + (-2188722313/10000000000 : ℝ)*x 1 + (5241833493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350156009/10000000000 : ℝ)^4239 ≤ (21918925599747/50000000000000 : ℝ)^3215 := by
    have hnat : (5350156009 : ℕ)^4239*50000000000000^3215 ≤ 21918925599747^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350156009 10000000000 21918925599747 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188722313/10000000000 : ℝ)^4239 ≤ (13490771132307/100000000000000 : ℝ)^3215 := by
    have hnat : (2188722313 : ℕ)^4239*100000000000000^3215 ≤ 13490771132307^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188722313 10000000000 13490771132307 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241833493/10000000000 : ℝ)^4239 ≤ (1333480551483/3125000000000 : ℝ)^3215 := by
    have hnat : (5241833493 : ℕ)^4239*3125000000000^3215 ≤ 1333480551483^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241833493 10000000000 1333480551483 3125000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350156009/10000000000 : ℝ), (-2188722313/10000000000 : ℝ), (5241833493/10000000000 : ℝ)] ![(21918925599747/50000000000000 : ℝ), (13490771132307/100000000000000 : ℝ), (1333480551483/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350156009/10000000000 : ℝ)|^4239 ≤ (21918925599747/50000000000000 : ℝ)^3215
        have hw : |(5350156009/10000000000 : ℝ)|=(5350156009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188722313/10000000000 : ℝ)|^4239 ≤ (13490771132307/100000000000000 : ℝ)^3215
        have hw : |(-2188722313/10000000000 : ℝ)|=(2188722313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241833493/10000000000 : ℝ)|^4239 ≤ (1333480551483/3125000000000 : ℝ)^3215
        have hw : |(5241833493/10000000000 : ℝ)|=(5241833493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350156079/10000000000 : ℝ)*x 0 + (1310458379/2500000000 : ℝ)*x 1 + (-2188722191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350156079/10000000000 : ℝ)^4239 ≤ (43837851955741/100000000000000 : ℝ)^3215 := by
    have hnat : (5350156079 : ℕ)^4239*100000000000000^3215 ≤ 43837851955741^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350156079 10000000000 43837851955741 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310458379/2500000000 : ℝ)^4239 ≤ (10667844473581/25000000000000 : ℝ)^3215 := by
    have hnat : (1310458379 : ℕ)^4239*25000000000000^3215 ≤ 10667844473581^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310458379 2500000000 10667844473581 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188722191/10000000000 : ℝ)^4239 ≤ (13490770140817/100000000000000 : ℝ)^3215 := by
    have hnat : (2188722191 : ℕ)^4239*100000000000000^3215 ≤ 13490770140817^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188722191 10000000000 13490770140817 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350156079/10000000000 : ℝ), (1310458379/2500000000 : ℝ), (-2188722191/10000000000 : ℝ)] ![(43837851955741/100000000000000 : ℝ), (10667844473581/25000000000000 : ℝ), (13490770140817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350156079/10000000000 : ℝ)|^4239 ≤ (43837851955741/100000000000000 : ℝ)^3215
        have hw : |(5350156079/10000000000 : ℝ)|=(5350156079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310458379/2500000000 : ℝ)|^4239 ≤ (10667844473581/25000000000000 : ℝ)^3215
        have hw : |(1310458379/2500000000 : ℝ)|=(1310458379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188722191/10000000000 : ℝ)|^4239 ≤ (13490770140817/100000000000000 : ℝ)^3215
        have hw : |(-2188722191/10000000000 : ℝ)|=(2188722191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343317711/10000000000 : ℝ)*x 0 + (1042029197/2500000000 : ℝ)*x 1 + (4525589599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343317711/10000000000 : ℝ)^4239 ≤ (4162701374987/12500000000000 : ℝ)^3215 := by
    have hnat : (4343317711 : ℕ)^4239*12500000000000^3215 ≤ 4162701374987^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343317711 10000000000 4162701374987 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042029197/2500000000 : ℝ)^4239 ≤ (7885478999359/25000000000000 : ℝ)^3215 := by
    have hnat : (1042029197 : ℕ)^4239*25000000000000^3215 ≤ 7885478999359^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042029197 2500000000 7885478999359 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525589599/10000000000 : ℝ)^4239 ≤ (35156472988561/100000000000000 : ℝ)^3215 := by
    have hnat : (4525589599 : ℕ)^4239*100000000000000^3215 ≤ 35156472988561^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525589599 10000000000 35156472988561 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343317711/10000000000 : ℝ), (1042029197/2500000000 : ℝ), (4525589599/10000000000 : ℝ)] ![(4162701374987/12500000000000 : ℝ), (7885478999359/25000000000000 : ℝ), (35156472988561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343317711/10000000000 : ℝ)|^4239 ≤ (4162701374987/12500000000000 : ℝ)^3215
        have hw : |(4343317711/10000000000 : ℝ)|=(4343317711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042029197/2500000000 : ℝ)|^4239 ≤ (7885478999359/25000000000000 : ℝ)^3215
        have hw : |(1042029197/2500000000 : ℝ)|=(1042029197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525589599/10000000000 : ℝ)|^4239 ≤ (35156472988561/100000000000000 : ℝ)^3215
        have hw : |(4525589599/10000000000 : ℝ)|=(4525589599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099605921/10000000000 : ℝ)*x 0 + (5242460819/10000000000 : ℝ)*x 1 + (135400081/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099605921/10000000000 : ℝ)^4239 ≤ (12771265415211/100000000000000 : ℝ)^3215 := by
    have hnat : (2099605921 : ℕ)^4239*100000000000000^3215 ≤ 12771265415211^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099605921 10000000000 12771265415211 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242460819/10000000000 : ℝ)^4239 ≤ (8535622218893/20000000000000 : ℝ)^3215 := by
    have hnat : (5242460819 : ℕ)^4239*20000000000000^3215 ≤ 8535622218893^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242460819 10000000000 8535622218893 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135400081/250000000 : ℝ)^4239 ≤ (44550623472171/100000000000000 : ℝ)^3215 := by
    have hnat : (135400081 : ℕ)^4239*100000000000000^3215 ≤ 44550623472171^3215*250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135400081 250000000 44550623472171 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099605921/10000000000 : ℝ), (5242460819/10000000000 : ℝ), (135400081/250000000 : ℝ)] ![(12771265415211/100000000000000 : ℝ), (8535622218893/20000000000000 : ℝ), (44550623472171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099605921/10000000000 : ℝ)|^4239 ≤ (12771265415211/100000000000000 : ℝ)^3215
        have hw : |(-2099605921/10000000000 : ℝ)|=(2099605921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242460819/10000000000 : ℝ)|^4239 ≤ (8535622218893/20000000000000 : ℝ)^3215
        have hw : |(5242460819/10000000000 : ℝ)|=(5242460819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135400081/250000000 : ℝ)|^4239 ≤ (44550623472171/100000000000000 : ℝ)^3215
        have hw : |(135400081/250000000 : ℝ)|=(135400081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305476899/10000000000 : ℝ)*x 0 + (-125909527/625000000 : ℝ)*x 1 + (5416003437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305476899/10000000000 : ℝ)^4239 ≤ (43355802738727/100000000000000 : ℝ)^3215 := by
    have hnat : (5305476899 : ℕ)^4239*100000000000000^3215 ≤ 43355802738727^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305476899 10000000000 43355802738727 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125909527/625000000 : ℝ)^4239 ≤ (12093571638949/100000000000000 : ℝ)^3215 := by
    have hnat : (125909527 : ℕ)^4239*100000000000000^3215 ≤ 12093571638949^3215*625000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125909527 625000000 12093571638949 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416003437/10000000000 : ℝ)^4239 ≤ (11137656402193/25000000000000 : ℝ)^3215 := by
    have hnat : (5416003437 : ℕ)^4239*25000000000000^3215 ≤ 11137656402193^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416003437 10000000000 11137656402193 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305476899/10000000000 : ℝ), (-125909527/625000000 : ℝ), (5416003437/10000000000 : ℝ)] ![(43355802738727/100000000000000 : ℝ), (12093571638949/100000000000000 : ℝ), (11137656402193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305476899/10000000000 : ℝ)|^4239 ≤ (43355802738727/100000000000000 : ℝ)^3215
        have hw : |(5305476899/10000000000 : ℝ)|=(5305476899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125909527/625000000 : ℝ)|^4239 ≤ (12093571638949/100000000000000 : ℝ)^3215
        have hw : |(-125909527/625000000 : ℝ)|=(125909527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416003437/10000000000 : ℝ)|^4239 ≤ (11137656402193/25000000000000 : ℝ)^3215
        have hw : |(5416003437/10000000000 : ℝ)|=(5416003437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326369319/2500000000 : ℝ)*x 0 + (10578131/19531250 : ℝ)*x 1 + (-100727621/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326369319/2500000000 : ℝ)^4239 ≤ (43355806800789/100000000000000 : ℝ)^3215 := by
    have hnat : (1326369319 : ℕ)^4239*100000000000000^3215 ≤ 43355806800789^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326369319 2500000000 43355806800789 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10578131/19531250 : ℝ)^4239 ≤ (22275310825047/50000000000000 : ℝ)^3215 := by
    have hnat : (10578131 : ℕ)^4239*50000000000000^3215 ≤ 22275310825047^3215*19531250^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10578131 19531250 22275310825047 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100727621/500000000 : ℝ)^4239 ≤ (12093571543967/100000000000000 : ℝ)^3215 := by
    have hnat : (100727621 : ℕ)^4239*100000000000000^3215 ≤ 12093571543967^3215*500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100727621 500000000 12093571543967 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326369319/2500000000 : ℝ), (10578131/19531250 : ℝ), (-100727621/500000000 : ℝ)] ![(43355806800789/100000000000000 : ℝ), (22275310825047/50000000000000 : ℝ), (12093571543967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326369319/2500000000 : ℝ)|^4239 ≤ (43355806800789/100000000000000 : ℝ)^3215
        have hw : |(1326369319/2500000000 : ℝ)|=(1326369319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10578131/19531250 : ℝ)|^4239 ≤ (22275310825047/50000000000000 : ℝ)^3215
        have hw : |(10578131/19531250 : ℝ)|=(10578131/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100727621/500000000 : ℝ)|^4239 ≤ (12093571543967/100000000000000 : ℝ)^3215
        have hw : |(-100727621/500000000 : ℝ)|=(100727621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s5_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343344171/10000000000 : ℝ)*x 0 + (226215327/500000000 : ℝ)*x 1 + (2084703493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343344171/10000000000 : ℝ)^4239 ≤ (33301878495313/100000000000000 : ℝ)^3215 := by
    have hnat : (4343344171 : ℕ)^4239*100000000000000^3215 ≤ 33301878495313^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343344171 10000000000 33301878495313 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226215327/500000000 : ℝ)^4239 ≤ (17571665825251/50000000000000 : ℝ)^3215 := by
    have hnat : (226215327 : ℕ)^4239*50000000000000^3215 ≤ 17571665825251^3215*500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226215327 500000000 17571665825251 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084703493/5000000000 : ℝ)^4239 ≤ (31554789846171/100000000000000 : ℝ)^3215 := by
    have hnat : (2084703493 : ℕ)^4239*100000000000000^3215 ≤ 31554789846171^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084703493 5000000000 31554789846171 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343344171/10000000000 : ℝ), (226215327/500000000 : ℝ), (2084703493/5000000000 : ℝ)] ![(33301878495313/100000000000000 : ℝ), (17571665825251/50000000000000 : ℝ), (31554789846171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343344171/10000000000 : ℝ)|^4239 ≤ (33301878495313/100000000000000 : ℝ)^3215
        have hw : |(4343344171/10000000000 : ℝ)|=(4343344171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226215327/500000000 : ℝ)|^4239 ≤ (17571665825251/50000000000000 : ℝ)^3215
        have hw : |(226215327/500000000 : ℝ)|=(226215327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084703493/5000000000 : ℝ)|^4239 ≤ (31554789846171/100000000000000 : ℝ)^3215
        have hw : |(2084703493/5000000000 : ℝ)|=(2084703493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5457/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (1304491462998923/12500000000000000000 : ℝ) := by
    have hpowers : (5457/50000 : ℝ)^2119 ≤ (1304491462998923/12500000000000000000 : ℝ)^512 := by
      have hnat : (5457 : ℕ)^2119*12500000000000000000^512 ≤ 1304491462998923^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5457 50000 1304491462998923 12500000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5457/50000 : ℝ)) (X := (1304491462998923/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (2119/512 : ℝ) ≤ (3627932349326167/10000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^2119 ≤ (3627932349326167/10000000000000000000 : ℝ)^512 := by
      have hnat : (3687 : ℕ)^2119*10000000000000000000^512 ≤ 3627932349326167^512*25000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 3627932349326167 10000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (3627932349326167/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251304491462998923/6250000000000000000 : ℝ) ≤ (2500126068291741/2500000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (6251304491462998923/6250000000000000000 : ℝ)^512 ≤ (2500126068291741/2500000000000000 : ℝ)^2119 := by
      have hnat : (6251304491462998923 : ℕ)^512*2500000000000000^2119 ≤ 2500126068291741^2119*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251304491462998923 6250000000000000000 2500126068291741 2500000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126068291741/2500000000000000 : ℝ)) (X := (6251304491462998923/6250000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023357627598626527/50000000000000000000 : ℝ) ≤ (62507053437641/62500000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50023357627598626527/50000000000000000000 : ℝ)^512 ≤ (62507053437641/62500000000000 : ℝ)^2119 := by
      have hnat : (50023357627598626527 : ℕ)^512*62500000000000^2119 ≤ 62507053437641^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023357627598626527 50000000000000000000 62507053437641 62500000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507053437641/62500000000000 : ℝ)) (X := (50023357627598626527/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003627932349326167/5000000000000000000 : ℝ) ≤ (2500438206719539/2500000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (5003627932349326167/5000000000000000000 : ℝ)^512 ≤ (2500438206719539/2500000000000000 : ℝ)^2119 := by
      have hnat : (5003627932349326167 : ℕ)^512*2500000000000000^2119 ≤ 2500438206719539^2119*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003627932349326167 5000000000000000000 2500438206719539 2500000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500438206719539/2500000000000000 : ℝ)) (X := (5003627932349326167/5000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1304491462998923/12500000000000000000 : ℝ) ≤ ((1597012777838257937/1597500000000000000 : ℝ)+2*(156069213899/95850000000000 : ℝ)*(5457/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1597012777838257937/1597500000000000000 : ℝ)+2*(156069213899/95850000000000 : ℝ)*(5457/50000 : ℝ)=(2500126068291741/2500000000000000 : ℝ) by norm_num, show 1+2*(1304491462998923/12500000000000000000 : ℝ)=(6251304491462998923/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3627932349326167/10000000000000000000 : ℝ)+(1304491462998923/12500000000000000000 : ℝ) ≤ ((1597012777838257937/1597500000000000000 : ℝ)+(156069213899/95850000000000 : ℝ)*((3687/25000 : ℝ)+(5457/50000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1597012777838257937/1597500000000000000 : ℝ)+(156069213899/95850000000000 : ℝ)*((3687/25000 : ℝ)+(5457/50000 : ℝ))=(62507053437641/62500000000000 : ℝ) by norm_num, show 1+(3627932349326167/10000000000000000000 : ℝ)+(1304491462998923/12500000000000000000 : ℝ)=(50023357627598626527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3627932349326167/10000000000000000000 : ℝ) ≤ ((1597012777838257937/1597500000000000000 : ℝ)+2*(156069213899/95850000000000 : ℝ)*(3687/25000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1597012777838257937/1597500000000000000 : ℝ)+2*(156069213899/95850000000000 : ℝ)*(3687/25000 : ℝ)=(2500438206719539/2500000000000000 : ℝ) by norm_num, show 1+2*(3627932349326167/10000000000000000000 : ℝ)=(5003627932349326167/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1597012777838257937/1597500000000000000 : ℝ)*(X 1 0+X 2 0)+(156069213899/95850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1597012777838257937/1597500000000000000 : ℝ)) (alpha := (156069213899/95850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1597012777838257937/1597500000000000000 : ℝ)*(X 0 1+X 2 1)+(156069213899/95850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1597012777838257937/1597500000000000000 : ℝ)) (alpha := (156069213899/95850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1597012777838257937/1597500000000000000 : ℝ)*(X 0 2+X 1 2)+(156069213899/95850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1597012777838257937/1597500000000000000 : ℝ)) (alpha := (156069213899/95850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419918597/2000000000 : ℝ)*X 0 0+(2708316831/5000000000 : ℝ)*X 0 1+(1048366693/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350156009/10000000000 : ℝ)*X 1 0+(-2188722313/10000000000 : ℝ)*X 1 1+(5241833493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350156079/10000000000 : ℝ)*X 2 0+(1310458379/2500000000 : ℝ)*X 2 1+(-2188722191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343317711/10000000000 : ℝ)*X 0 0+(1042029197/2500000000 : ℝ)*X 0 1+(4525589599/10000000000 : ℝ)*X 0 2+(4343317711/10000000000 : ℝ)*X 1 0+(1042029197/2500000000 : ℝ)*X 1 1+(4525589599/10000000000 : ℝ)*X 1 2+(4343317711/10000000000 : ℝ)*X 2 0+(1042029197/2500000000 : ℝ)*X 2 1+(4525589599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2099605921/10000000000 : ℝ)*X 0 0+(5242460819/10000000000 : ℝ)*X 0 1+(135400081/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305476899/10000000000 : ℝ)*X 1 0+(-125909527/625000000 : ℝ)*X 1 1+(5416003437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326369319/2500000000 : ℝ)*X 2 0+(10578131/19531250 : ℝ)*X 2 1+(-100727621/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343344171/10000000000 : ℝ)*X 0 0+(226215327/500000000 : ℝ)*X 0 1+(2084703493/5000000000 : ℝ)*X 0 2+(4343344171/10000000000 : ℝ)*X 1 0+(226215327/500000000 : ℝ)*X 1 1+(2084703493/5000000000 : ℝ)*X 1 2+(4343344171/10000000000 : ℝ)*X 2 0+(226215327/500000000 : ℝ)*X 2 1+(2084703493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11100547051483046289449401/1109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2196543437/100000000000000 : ℝ)*(base19) + (106379279/5000000000000 : ℝ)*(base23) + (19234949/25000000000000 : ℝ)*(lower2) + (2610569/800000000000 : ℝ)*(upper3) + (3772829/1000000000000 : ℝ)*(upper5) + (1064794735361469/25000000000000 : ℝ)*(major0) + (1064794735361469/25000000000000 : ℝ)*(major1) + (1064794735361469/25000000000000 : ℝ)*(major2) + (2860427599730113/50000000000000 : ℝ)*(sp0) + (1430223798617483/25000000000000 : ℝ)*(sp1) + (5720895263427789/100000000000000 : ℝ)*(sp2) + (2797437720827429/100000000000000 : ℝ)*(sp3) + (42191553143/100000000000000 : ℝ)*(sp4) + (1121875669/5000000000000 : ℝ)*(sp7) + (349682519792601/12500000000000 : ℝ)*(f.failure) + (5720897391013369/100000000000000 : ℝ)*(f.sum) + (2748483932377/1597500000000000000000000000 : ℝ)*base66 + (112653980056608047/39937500000000000000000000000000 : ℝ)*base68 + (516941894814108047/39937500000000000000000000000000 : ℝ)*base70 + (468505468208733047/39937500000000000000000000000000 : ℝ)*base72 + (538967060969/199687500000000000000000000 : ℝ)*base74 + (591899386675016953/39937500000000000000000000000000 : ℝ)*base75 + (525866019807295547/39937500000000000000000000000000 : ℝ)*base78 + (276814853081920547/39937500000000000000000000000000 : ℝ)*base80 + (1028718116297/399375000000000000000000000 : ℝ)*base81 + (7676961/1250000000000000000000 : ℝ)*base90 + (7676961/1250000000000000000000 : ℝ)*base92 + (7676961/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8487012079938570869696647/832031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (90065129/6250000000000 : ℝ)*(base19) + (404503489/20000000000000 : ℝ)*(base23) + (8261761/5000000000000 : ℝ)*(upper3) + (79882043/100000000000000 : ℝ)*(lower4) + (262392987/100000000000000 : ℝ)*(upper5) + (536248956525517/12500000000000 : ℝ)*(major0) + (536248956525517/12500000000000 : ℝ)*(major1) + (536248956525517/12500000000000 : ℝ)*(major2) + (34957522733/100000000000000 : ℝ)*(sp1) + (9376225749/25000000000000 : ℝ)*(sp2) + (2881142395127301/50000000000000 : ℝ)*(sp4) + (1152449678337961/20000000000000 : ℝ)*(sp5) + (5762245262834161/100000000000000 : ℝ)*(sp6) + (352212271767739/12500000000000 : ℝ)*(sp7) + (352212271767739/12500000000000 : ℝ)*(f.failure) + (2881142395127301/50000000000000 : ℝ)*(f.sum) + (13487937962089/4792500000000000000000000000 : ℝ)*base65 + (31724298868797787/59906250000000000000000000000000 : ℝ)*base67 + (97946812621985287/59906250000000000000000000000000 : ℝ)*base69 + (198610008314360287/59906250000000000000000000000000 : ℝ)*base71 + (5695155588293/9585000000000000000000000000 : ℝ)*base73 + (372961688963922787/59906250000000000000000000000000 : ℝ)*base75 + (127838512149485287/59906250000000000000000000000000 : ℝ)*base77 + (142867316733485287/59906250000000000000000000000000 : ℝ)*base79 + (3037419216473/599062500000000000000000000 : ℝ)*base81 + (9925779/1250000000000000000000 : ℝ)*base90 + (9925779/1250000000000000000000 : ℝ)*base92 + (9925779/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1279_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1279_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1279_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1279_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (294/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
