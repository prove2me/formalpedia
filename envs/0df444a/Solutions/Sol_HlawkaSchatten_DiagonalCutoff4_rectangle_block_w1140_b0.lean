-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:33.178194+00:00
-- url     : https://prove2.me/submissions/cfb151bf-cca7-4601-81d0-127bfd0b8be7

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
theorem support_rectangle_w1140_s0_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-946221933/5000000000 : ℝ)*x 0 + (1210958511/2000000000 : ℝ)*x 1 + (4780219319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946221933/5000000000 : ℝ)^8333 ≤ (2200225436497/20000000000000 : ℝ)^6285 := by
    have hnat : (946221933 : ℕ)^8333*20000000000000^6285 ≤ 2200225436497^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946221933 5000000000 2200225436497 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210958511/2000000000 : ℝ)^8333 ≤ (51415632100419/100000000000000 : ℝ)^6285 := by
    have hnat : (1210958511 : ℕ)^8333*100000000000000^6285 ≤ 51415632100419^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210958511 2000000000 51415632100419 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780219319/10000000000 : ℝ)^8333 ≤ (37583240702079/100000000000000 : ℝ)^6285 := by
    have hnat : (4780219319 : ℕ)^8333*100000000000000^6285 ≤ 37583240702079^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780219319 10000000000 37583240702079 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946221933/5000000000 : ℝ), (1210958511/2000000000 : ℝ), (4780219319/10000000000 : ℝ)] ![(2200225436497/20000000000000 : ℝ), (51415632100419/100000000000000 : ℝ), (37583240702079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946221933/5000000000 : ℝ)|^8333 ≤ (2200225436497/20000000000000 : ℝ)^6285
        have hw : |(-946221933/5000000000 : ℝ)|=(946221933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1210958511/2000000000 : ℝ)|^8333 ≤ (51415632100419/100000000000000 : ℝ)^6285
        have hw : |(1210958511/2000000000 : ℝ)|=(1210958511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780219319/10000000000 : ℝ)|^8333 ≤ (37583240702079/100000000000000 : ℝ)^6285
        have hw : |(4780219319/10000000000 : ℝ)|=(4780219319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516906271/10000000000 : ℝ)*x 0 + (-2623956571/10000000000 : ℝ)*x 1 + (298763707/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516906271/10000000000 : ℝ)^8333 ≤ (11362287692561/25000000000000 : ℝ)^6285 := by
    have hnat : (5516906271 : ℕ)^8333*25000000000000^6285 ≤ 11362287692561^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516906271 10000000000 11362287692561 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623956571/10000000000 : ℝ)^8333 ≤ (16967608582963/100000000000000 : ℝ)^6285 := by
    have hnat : (2623956571 : ℕ)^8333*100000000000000^6285 ≤ 16967608582963^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623956571 10000000000 16967608582963 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298763707/625000000 : ℝ)^8333 ≤ (3758324062911/10000000000000 : ℝ)^6285 := by
    have hnat : (298763707 : ℕ)^8333*10000000000000^6285 ≤ 3758324062911^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298763707 625000000 3758324062911 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516906271/10000000000 : ℝ), (-2623956571/10000000000 : ℝ), (298763707/625000000 : ℝ)] ![(11362287692561/25000000000000 : ℝ), (16967608582963/100000000000000 : ℝ), (3758324062911/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516906271/10000000000 : ℝ)|^8333 ≤ (11362287692561/25000000000000 : ℝ)^6285
        have hw : |(5516906271/10000000000 : ℝ)|=(5516906271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2623956571/10000000000 : ℝ)|^8333 ≤ (16967608582963/100000000000000 : ℝ)^6285
        have hw : |(-2623956571/10000000000 : ℝ)|=(2623956571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298763707/625000000 : ℝ)|^8333 ≤ (3758324062911/10000000000000 : ℝ)^6285
        have hw : |(298763707/625000000 : ℝ)|=(298763707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516906351/10000000000 : ℝ)*x 0 + (956043851/2000000000 : ℝ)*x 1 + (-2623956539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516906351/10000000000 : ℝ)^8333 ≤ (11362287911013/25000000000000 : ℝ)^6285 := by
    have hnat : (5516906351 : ℕ)^8333*25000000000000^6285 ≤ 11362287911013^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516906351 10000000000 11362287911013 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956043851/2000000000 : ℝ)^8333 ≤ (37583240034931/100000000000000 : ℝ)^6285 := by
    have hnat : (956043851 : ℕ)^8333*100000000000000^6285 ≤ 37583240034931^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956043851 2000000000 37583240034931 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623956539/10000000000 : ℝ)^8333 ≤ (1696760830861/10000000000000 : ℝ)^6285 := by
    have hnat : (2623956539 : ℕ)^8333*10000000000000^6285 ≤ 1696760830861^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623956539 10000000000 1696760830861 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516906351/10000000000 : ℝ), (956043851/2000000000 : ℝ), (-2623956539/10000000000 : ℝ)] ![(11362287911013/25000000000000 : ℝ), (37583240034931/100000000000000 : ℝ), (1696760830861/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516906351/10000000000 : ℝ)|^8333 ≤ (11362287911013/25000000000000 : ℝ)^6285
        have hw : |(5516906351/10000000000 : ℝ)|=(5516906351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956043851/2000000000 : ℝ)|^8333 ≤ (37583240034931/100000000000000 : ℝ)^6285
        have hw : |(956043851/2000000000 : ℝ)|=(956043851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2623956539/10000000000 : ℝ)|^8333 ≤ (1696760830861/10000000000000 : ℝ)^6285
        have hw : |(-2623956539/10000000000 : ℝ)|=(2623956539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4201152593/10000000000 : ℝ)*x 0 + (3121171219/10000000000 : ℝ)*x 1 + (2827953609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201152593/10000000000 : ℝ)^8333 ≤ (3958686572557/12500000000000 : ℝ)^6285 := by
    have hnat : (4201152593 : ℕ)^8333*12500000000000^6285 ≤ 3958686572557^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201152593 10000000000 3958686572557 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121171219/10000000000 : ℝ)^8333 ≤ (21356906502067/100000000000000 : ℝ)^6285 := by
    have hnat : (3121171219 : ℕ)^8333*100000000000000^6285 ≤ 21356906502067^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121171219 10000000000 21356906502067 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2827953609/5000000000 : ℝ)^8333 ≤ (46973600903483/100000000000000 : ℝ)^6285 := by
    have hnat : (2827953609 : ℕ)^8333*100000000000000^6285 ≤ 46973600903483^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827953609 5000000000 46973600903483 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201152593/10000000000 : ℝ), (3121171219/10000000000 : ℝ), (2827953609/5000000000 : ℝ)] ![(3958686572557/12500000000000 : ℝ), (21356906502067/100000000000000 : ℝ), (46973600903483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201152593/10000000000 : ℝ)|^8333 ≤ (3958686572557/12500000000000 : ℝ)^6285
        have hw : |(4201152593/10000000000 : ℝ)|=(4201152593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121171219/10000000000 : ℝ)|^8333 ≤ (21356906502067/100000000000000 : ℝ)^6285
        have hw : |(3121171219/10000000000 : ℝ)|=(3121171219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2827953609/5000000000 : ℝ)|^8333 ≤ (46973600903483/100000000000000 : ℝ)^6285
        have hw : |(2827953609/5000000000 : ℝ)|=(2827953609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897595349/10000000000 : ℝ)*x 0 + (1203275167/2500000000 : ℝ)*x 1 + (1505188817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897595349/10000000000 : ℝ)^8333 ≤ (1380106192363/12500000000000 : ℝ)^6285 := by
    have hnat : (1897595349 : ℕ)^8333*12500000000000^6285 ≤ 1380106192363^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897595349 10000000000 1380106192363 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203275167/2500000000 : ℝ)^8333 ≤ (3792638582377/10000000000000 : ℝ)^6285 := by
    have hnat : (1203275167 : ℕ)^8333*10000000000000^6285 ≤ 3792638582377^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203275167 2500000000 3792638582377 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1505188817/2500000000 : ℝ)^8333 ≤ (51032764612563/100000000000000 : ℝ)^6285 := by
    have hnat : (1505188817 : ℕ)^8333*100000000000000^6285 ≤ 51032764612563^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505188817 2500000000 51032764612563 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897595349/10000000000 : ℝ), (1203275167/2500000000 : ℝ), (1505188817/2500000000 : ℝ)] ![(1380106192363/12500000000000 : ℝ), (3792638582377/10000000000000 : ℝ), (51032764612563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897595349/10000000000 : ℝ)|^8333 ≤ (1380106192363/12500000000000 : ℝ)^6285
        have hw : |(-1897595349/10000000000 : ℝ)|=(1897595349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203275167/2500000000 : ℝ)|^8333 ≤ (3792638582377/10000000000000 : ℝ)^6285
        have hw : |(1203275167/2500000000 : ℝ)|=(1203275167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1505188817/2500000000 : ℝ)|^8333 ≤ (51032764612563/100000000000000 : ℝ)^6285
        have hw : |(1505188817/2500000000 : ℝ)|=(1505188817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170586033/10000000000 : ℝ)*x 0 + (-345855161/2500000000 : ℝ)*x 1 + (1204151029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170586033/10000000000 : ℝ)^8333 ≤ (10426420072437/25000000000000 : ℝ)^6285 := by
    have hnat : (5170586033 : ℕ)^8333*25000000000000^6285 ≤ 10426420072437^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170586033 10000000000 10426420072437 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345855161/2500000000 : ℝ)^8333 ≤ (7261556466841/100000000000000 : ℝ)^6285 := by
    have hnat : (345855161 : ℕ)^8333*100000000000000^6285 ≤ 7261556466841^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345855161 2500000000 7261556466841 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204151029/2000000000 : ℝ)^8333 ≤ (51032763230273/100000000000000 : ℝ)^6285 := by
    have hnat : (1204151029 : ℕ)^8333*100000000000000^6285 ≤ 51032763230273^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204151029 2000000000 51032763230273 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170586033/10000000000 : ℝ), (-345855161/2500000000 : ℝ), (1204151029/2000000000 : ℝ)] ![(10426420072437/25000000000000 : ℝ), (7261556466841/100000000000000 : ℝ), (51032763230273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170586033/10000000000 : ℝ)|^8333 ≤ (10426420072437/25000000000000 : ℝ)^6285
        have hw : |(5170586033/10000000000 : ℝ)|=(5170586033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345855161/2500000000 : ℝ)|^8333 ≤ (7261556466841/100000000000000 : ℝ)^6285
        have hw : |(-345855161/2500000000 : ℝ)|=(345855161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204151029/2000000000 : ℝ)|^8333 ≤ (51032763230273/100000000000000 : ℝ)^6285
        have hw : |(1204151029/2000000000 : ℝ)|=(1204151029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170586041/10000000000 : ℝ)*x 0 + (6020755163/10000000000 : ℝ)*x 1 + (-691710301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170586041/10000000000 : ℝ)^8333 ≤ (20852840187651/50000000000000 : ℝ)^6285 := by
    have hnat : (5170586041 : ℕ)^8333*50000000000000^6285 ≤ 20852840187651^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170586041 10000000000 20852840187651 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6020755163/10000000000 : ℝ)^8333 ≤ (51032763432559/100000000000000 : ℝ)^6285 := by
    have hnat : (6020755163 : ℕ)^8333*100000000000000^6285 ≤ 51032763432559^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020755163 10000000000 51032763432559 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691710301/5000000000 : ℝ)^8333 ≤ (3630778087273/50000000000000 : ℝ)^6285 := by
    have hnat : (691710301 : ℕ)^8333*50000000000000^6285 ≤ 3630778087273^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691710301 5000000000 3630778087273 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170586041/10000000000 : ℝ), (6020755163/10000000000 : ℝ), (-691710301/5000000000 : ℝ)] ![(20852840187651/50000000000000 : ℝ), (51032763432559/100000000000000 : ℝ), (3630778087273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170586041/10000000000 : ℝ)|^8333 ≤ (20852840187651/50000000000000 : ℝ)^6285
        have hw : |(5170586041/10000000000 : ℝ)|=(5170586041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6020755163/10000000000 : ℝ)|^8333 ≤ (51032763432559/100000000000000 : ℝ)^6285
        have hw : |(6020755163/10000000000 : ℝ)|=(6020755163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691710301/5000000000 : ℝ)|^8333 ≤ (3630778087273/50000000000000 : ℝ)^6285
        have hw : |(-691710301/5000000000 : ℝ)|=(691710301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s0_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4211397469/10000000000 : ℝ)*x 0 + (1118103199/2000000000 : ℝ)*x 1 + (1594430609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211397469/10000000000 : ℝ)^8333 ≤ (6354385492757/20000000000000 : ℝ)^6285 := by
    have hnat : (4211397469 : ℕ)^8333*20000000000000^6285 ≤ 6354385492757^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211397469 10000000000 6354385492757 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118103199/2000000000 : ℝ)^8333 ≤ (11563725846439/25000000000000 : ℝ)^6285 := by
    have hnat : (1118103199 : ℕ)^8333*25000000000000^6285 ≤ 11563725846439^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118103199 2000000000 11563725846439 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594430609/5000000000 : ℝ)^8333 ≤ (21973169137899/100000000000000 : ℝ)^6285 := by
    have hnat : (1594430609 : ℕ)^8333*100000000000000^6285 ≤ 21973169137899^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594430609 5000000000 21973169137899 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211397469/10000000000 : ℝ), (1118103199/2000000000 : ℝ), (1594430609/5000000000 : ℝ)] ![(6354385492757/20000000000000 : ℝ), (11563725846439/25000000000000 : ℝ), (21973169137899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211397469/10000000000 : ℝ)|^8333 ≤ (6354385492757/20000000000000 : ℝ)^6285
        have hw : |(4211397469/10000000000 : ℝ)|=(4211397469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118103199/2000000000 : ℝ)|^8333 ≤ (11563725846439/25000000000000 : ℝ)^6285
        have hw : |(1118103199/2000000000 : ℝ)|=(1118103199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594430609/5000000000 : ℝ)|^8333 ≤ (21973169137899/100000000000000 : ℝ)^6285
        have hw : |(1594430609/5000000000 : ℝ)|=(1594430609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (81/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27823/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2083/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2083 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2083*1^512 ≤ 0^512*1^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2083/512 : ℝ) ≤ (601141960985167149/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2083 ≤ (601141960985167149/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2083*25000000000000000000^512 ≤ 601141960985167149^512*5^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 601141960985167149 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (601141960985167149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2083 := by
      have hnat : (1 : ℕ)^512*1^2083 ≤ 1^2083*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25601141960985167149/25000000000000000000 : ℝ) ≤ (10058575594390419/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (25601141960985167149/25000000000000000000 : ℝ)^512 ≤ (10058575594390419/10000000000000000 : ℝ)^2083 := by
      have hnat : (25601141960985167149 : ℕ)^512*10000000000000000^2083 ≤ 10058575594390419^2083*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25601141960985167149 25000000000000000000 10058575594390419 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058575594390419/10000000000000000 : ℝ)) (X := (25601141960985167149/25000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13101141960985167149/12500000000000000000 : ℝ) ≤ (5058575594390419/5000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (13101141960985167149/12500000000000000000 : ℝ)^512 ≤ (5058575594390419/5000000000000000 : ℝ)^2083 := by
      have hnat : (13101141960985167149 : ℕ)^512*5000000000000000^2083 ≤ 5058575594390419^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13101141960985167149 12500000000000000000 5058575594390419 5000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058575594390419/5000000000000000 : ℝ)) (X := (13101141960985167149/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58575594390419/4000000000000000 : ℝ)*(0 : ℝ))^(2083/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(58575594390419/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(601141960985167149/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58575594390419/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (1 : ℝ)+(58575594390419/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058575594390419/10000000000000000 : ℝ) by norm_num, show 1+(601141960985167149/25000000000000000000 : ℝ)+(0 : ℝ)=(25601141960985167149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(601141960985167149/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58575594390419/4000000000000000 : ℝ)*(2/5 : ℝ))^(2083/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(58575594390419/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058575594390419/5000000000000000 : ℝ) by norm_num, show 1+2*(601141960985167149/25000000000000000000 : ℝ)=(13101141960985167149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58575594390419/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58575594390419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58575594390419/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58575594390419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58575594390419/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58575594390419/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-946221933/5000000000 : ℝ)*X 0 0+(1210958511/2000000000 : ℝ)*X 0 1+(4780219319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516906271/10000000000 : ℝ)*X 1 0+(-2623956571/10000000000 : ℝ)*X 1 1+(298763707/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516906351/10000000000 : ℝ)*X 2 0+(956043851/2000000000 : ℝ)*X 2 1+(-2623956539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201152593/10000000000 : ℝ)*X 0 0+(3121171219/10000000000 : ℝ)*X 0 1+(2827953609/5000000000 : ℝ)*X 0 2+(4201152593/10000000000 : ℝ)*X 1 0+(3121171219/10000000000 : ℝ)*X 1 1+(2827953609/5000000000 : ℝ)*X 1 2+(4201152593/10000000000 : ℝ)*X 2 0+(3121171219/10000000000 : ℝ)*X 2 1+(2827953609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1897595349/10000000000 : ℝ)*X 0 0+(1203275167/2500000000 : ℝ)*X 0 1+(1505188817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170586033/10000000000 : ℝ)*X 1 0+(-345855161/2500000000 : ℝ)*X 1 1+(1204151029/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170586041/10000000000 : ℝ)*X 2 0+(6020755163/10000000000 : ℝ)*X 2 1+(-691710301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211397469/10000000000 : ℝ)*X 0 0+(1118103199/2000000000 : ℝ)*X 0 1+(1594430609/5000000000 : ℝ)*X 0 2+(4211397469/10000000000 : ℝ)*X 1 0+(1118103199/2000000000 : ℝ)*X 1 1+(1594430609/5000000000 : ℝ)*X 1 2+(4211397469/10000000000 : ℝ)*X 2 0+(1118103199/2000000000 : ℝ)*X 2 1+(1594430609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77618152335215096158911/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68725651/100000000000000 : ℝ)*(base1) + (1508220143/100000000000000 : ℝ)*(base19) + (1412017697/100000000000000 : ℝ)*(base23) + (10757959/10000000000000 : ℝ)*(base24) + (86748627/25000000000000 : ℝ)*(upper3) + (73694213478341/12500000000000 : ℝ)*(major0) + (73694213478341/12500000000000 : ℝ)*(major1) + (73694213478341/12500000000000 : ℝ)*(major2) + (392290666924791/50000000000000 : ℝ)*(sp0) + (784583036629393/100000000000000 : ℝ)*(sp1) + (784583025252249/100000000000000 : ℝ)*(sp2) + (394519946740747/100000000000000 : ℝ)*(sp3) + (655945121/20000000000000 : ℝ)*(sp4) + (2648355777/100000000000000 : ℝ)*(sp7) + (197261331911087/50000000000000 : ℝ)*(f.failure) + (6129566756637/781250000000 : ℝ)*(f.sum) + (92667451260121/25000000000000000000000000000 : ℝ)*base66 + (299947438485121/50000000000000000000000000000 : ℝ)*base68 + (233072447085121/50000000000000000000000000000 : ℝ)*base70 + (167246389935121/50000000000000000000000000000 : ℝ)*base72 + (116309003210121/25000000000000000000000000000 : ℝ)*base74 + (402608737985121/50000000000000000000000000000 : ℝ)*base76 + (414271884735121/50000000000000000000000000000 : ℝ)*base78 + (451756855735121/50000000000000000000000000000 : ℝ)*base80 + (108297496110121/25000000000000000000000000000 : ℝ)*base82 + (2325231/5000000000000000000000 : ℝ)*base90 + (2325231/5000000000000000000000 : ℝ)*base92 + (2325231/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (707763104528066252371869/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86690157/100000000000000 : ℝ)*(base1) + (1745753357/100000000000000 : ℝ)*(base19) + (1746379/100000000000 : ℝ)*(base23) + (191282109/100000000000000 : ℝ)*(upper3) + (204169107/100000000000000 : ℝ)*(upper5) + (622215596623483/100000000000000 : ℝ)*(major0) + (622215596623483/100000000000000 : ℝ)*(major1) + (622215596623483/100000000000000 : ℝ)*(major2) + (1777525617/50000000000000 : ℝ)*(sp1) + (443157931/12500000000000 : ℝ)*(sp2) + (414025707074551/50000000000000 : ℝ)*(sp4) + (828046026654353/100000000000000 : ℝ)*(sp5) + (828046035816497/100000000000000 : ℝ)*(sp6) + (16655181727073/4000000000000 : ℝ)*(sp7) + (208189814933491/50000000000000 : ℝ)*(f.failure) + (165610265491789/20000000000000 : ℝ)*(f.sum) + (46746180209377/200000000000000000000000000000 : ℝ)*base65 + (203354358790623/400000000000000000000000000000 : ℝ)*base68 + (1156955171209377/400000000000000000000000000000 : ℝ)*base69 + (2923773650409377/400000000000000000000000000000 : ℝ)*base71 + (575346740190623/200000000000000000000000000000 : ℝ)*base74 + (4647492028409377/400000000000000000000000000000 : ℝ)*base75 + (173720974390623/400000000000000000000000000000 : ℝ)*base78 + (627519595209377/400000000000000000000000000000 : ℝ)*base79 + (690029008809377/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3402317/5000000000000000000000 : ℝ)*base89 + (3402317/5000000000000000000000 : ℝ)*base91 + (3402317/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1140_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (81/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27823/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s1_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-419450089/2000000000 : ℝ)*x 0 + (1140410201/2000000000 : ℝ)*x 1 + (125046079/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419450089/2000000000 : ℝ)^8333 ≤ (6303423891931/50000000000000 : ℝ)^6285 := by
    have hnat : (419450089 : ℕ)^8333*50000000000000^6285 ≤ 6303423891931^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419450089 2000000000 6303423891931 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140410201/2000000000 : ℝ)^8333 ≤ (47482388785243/100000000000000 : ℝ)^6285 := by
    have hnat : (1140410201 : ℕ)^8333*100000000000000^6285 ≤ 47482388785243^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140410201 2000000000 47482388785243 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125046079/250000000 : ℝ)^8333 ≤ (7982152683651/20000000000000 : ℝ)^6285 := by
    have hnat : (125046079 : ℕ)^8333*20000000000000^6285 ≤ 7982152683651^6285*250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125046079 250000000 7982152683651 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419450089/2000000000 : ℝ), (1140410201/2000000000 : ℝ), (125046079/250000000 : ℝ)] ![(6303423891931/50000000000000 : ℝ), (47482388785243/100000000000000 : ℝ), (7982152683651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419450089/2000000000 : ℝ)|^8333 ≤ (6303423891931/50000000000000 : ℝ)^6285
        have hw : |(-419450089/2000000000 : ℝ)|=(419450089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140410201/2000000000 : ℝ)|^8333 ≤ (47482388785243/100000000000000 : ℝ)^6285
        have hw : |(1140410201/2000000000 : ℝ)|=(1140410201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125046079/250000000 : ℝ)|^8333 ≤ (7982152683651/20000000000000 : ℝ)^6285
        have hw : |(125046079/250000000 : ℝ)|=(125046079/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709617053/5000000000 : ℝ)*x 0 + (-123758011/500000000 : ℝ)*x 1 + (5001842507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709617053/5000000000 : ℝ)^8333 ≤ (22192702905739/50000000000000 : ℝ)^6285 := by
    have hnat : (2709617053 : ℕ)^8333*50000000000000^6285 ≤ 22192702905739^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709617053 5000000000 22192702905739 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123758011/500000000 : ℝ)^8333 ≤ (15703837674237/100000000000000 : ℝ)^6285 := by
    have hnat : (123758011 : ℕ)^8333*100000000000000^6285 ≤ 15703837674237^6285*500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123758011 500000000 15703837674237 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5001842507/10000000000 : ℝ)^8333 ≤ (19955378254993/50000000000000 : ℝ)^6285 := by
    have hnat : (5001842507 : ℕ)^8333*50000000000000^6285 ≤ 19955378254993^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001842507 10000000000 19955378254993 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709617053/5000000000 : ℝ), (-123758011/500000000 : ℝ), (5001842507/10000000000 : ℝ)] ![(22192702905739/50000000000000 : ℝ), (15703837674237/100000000000000 : ℝ), (19955378254993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709617053/5000000000 : ℝ)|^8333 ≤ (22192702905739/50000000000000 : ℝ)^6285
        have hw : |(2709617053/5000000000 : ℝ)|=(2709617053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123758011/500000000 : ℝ)|^8333 ≤ (15703837674237/100000000000000 : ℝ)^6285
        have hw : |(-123758011/500000000 : ℝ)|=(123758011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5001842507/10000000000 : ℝ)|^8333 ≤ (19955378254993/50000000000000 : ℝ)^6285
        have hw : |(5001842507/10000000000 : ℝ)|=(5001842507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419236011/10000000000 : ℝ)*x 0 + (5001840811/10000000000 : ℝ)*x 1 + (-618789973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419236011/10000000000 : ℝ)^8333 ≤ (44385426498281/100000000000000 : ℝ)^6285 := by
    have hnat : (5419236011 : ℕ)^8333*100000000000000^6285 ≤ 44385426498281^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419236011 10000000000 44385426498281 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001840811/10000000000 : ℝ)^8333 ≤ (39910738567531/100000000000000 : ℝ)^6285 := by
    have hnat : (5001840811 : ℕ)^8333*100000000000000^6285 ≤ 39910738567531^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001840811 10000000000 39910738567531 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618789973/2500000000 : ℝ)^8333 ≤ (7851917457553/50000000000000 : ℝ)^6285 := by
    have hnat : (618789973 : ℕ)^8333*50000000000000^6285 ≤ 7851917457553^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618789973 2500000000 7851917457553 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419236011/10000000000 : ℝ), (5001840811/10000000000 : ℝ), (-618789973/2500000000 : ℝ)] ![(44385426498281/100000000000000 : ℝ), (39910738567531/100000000000000 : ℝ), (7851917457553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419236011/10000000000 : ℝ)|^8333 ≤ (44385426498281/100000000000000 : ℝ)^6285
        have hw : |(5419236011/10000000000 : ℝ)|=(5419236011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001840811/10000000000 : ℝ)|^8333 ≤ (39910738567531/100000000000000 : ℝ)^6285
        have hw : |(5001840811/10000000000 : ℝ)|=(5001840811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-618789973/2500000000 : ℝ)|^8333 ≤ (7851917457553/50000000000000 : ℝ)^6285
        have hw : |(-618789973/2500000000 : ℝ)|=(618789973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (863521189/2000000000 : ℝ)*x 0 + (229790563/625000000 : ℝ)*x 1 + (5069145371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863521189/2000000000 : ℝ)^8333 ≤ (16419315169423/50000000000000 : ℝ)^6285 := by
    have hnat : (863521189 : ℕ)^8333*50000000000000^6285 ≤ 16419315169423^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863521189 2000000000 16419315169423 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229790563/625000000 : ℝ)^8333 ≤ (26537041137843/100000000000000 : ℝ)^6285 := by
    have hnat : (229790563 : ℕ)^8333*100000000000000^6285 ≤ 26537041137843^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229790563 625000000 26537041137843 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069145371/10000000000 : ℝ)^8333 ≤ (8124865699781/20000000000000 : ℝ)^6285 := by
    have hnat : (5069145371 : ℕ)^8333*20000000000000^6285 ≤ 8124865699781^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069145371 10000000000 8124865699781 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863521189/2000000000 : ℝ), (229790563/625000000 : ℝ), (5069145371/10000000000 : ℝ)] ![(16419315169423/50000000000000 : ℝ), (26537041137843/100000000000000 : ℝ), (8124865699781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863521189/2000000000 : ℝ)|^8333 ≤ (16419315169423/50000000000000 : ℝ)^6285
        have hw : |(863521189/2000000000 : ℝ)|=(863521189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229790563/625000000 : ℝ)|^8333 ≤ (26537041137843/100000000000000 : ℝ)^6285
        have hw : |(229790563/625000000 : ℝ)|=(229790563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069145371/10000000000 : ℝ)|^8333 ≤ (8124865699781/20000000000000 : ℝ)^6285
        have hw : |(5069145371/10000000000 : ℝ)|=(5069145371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049029897/5000000000 : ℝ)*x 0 + (313213197/625000000 : ℝ)*x 1 + (1423073263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049029897/5000000000 : ℝ)^8333 ≤ (12613298611699/100000000000000 : ℝ)^6285 := by
    have hnat : (1049029897 : ℕ)^8333*100000000000000^6285 ≤ 12613298611699^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049029897 5000000000 12613298611699 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (313213197/625000000 : ℝ)^8333 ≤ (4001201740759/10000000000000 : ℝ)^6285 := by
    have hnat : (313213197 : ℕ)^8333*10000000000000^6285 ≤ 4001201740759^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313213197 625000000 4001201740759 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423073263/2500000000 : ℝ)^8333 ≤ (11843670991843/25000000000000 : ℝ)^6285 := by
    have hnat : (1423073263 : ℕ)^8333*25000000000000^6285 ≤ 11843670991843^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423073263 2500000000 11843670991843 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049029897/5000000000 : ℝ), (313213197/625000000 : ℝ), (1423073263/2500000000 : ℝ)] ![(12613298611699/100000000000000 : ℝ), (4001201740759/10000000000000 : ℝ), (11843670991843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049029897/5000000000 : ℝ)|^8333 ≤ (12613298611699/100000000000000 : ℝ)^6285
        have hw : |(-1049029897/5000000000 : ℝ)|=(1049029897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(313213197/625000000 : ℝ)|^8333 ≤ (4001201740759/10000000000000 : ℝ)^6285
        have hw : |(313213197/625000000 : ℝ)|=(313213197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423073263/2500000000 : ℝ)|^8333 ≤ (11843670991843/25000000000000 : ℝ)^6285
        have hw : |(1423073263/2500000000 : ℝ)|=(1423073263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239731427/10000000000 : ℝ)*x 0 + (-178470941/1000000000 : ℝ)*x 1 + (5692292727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239731427/10000000000 : ℝ)^8333 ≤ (42446746801053/100000000000000 : ℝ)^6285 := by
    have hnat : (5239731427 : ℕ)^8333*100000000000000^6285 ≤ 42446746801053^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239731427 10000000000 42446746801053 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178470941/1000000000 : ℝ)^8333 ≤ (5089286407527/50000000000000 : ℝ)^6285 := by
    have hnat : (178470941 : ℕ)^8333*50000000000000^6285 ≤ 5089286407527^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178470941 1000000000 5089286407527 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5692292727/10000000000 : ℝ)^8333 ≤ (47374680381139/100000000000000 : ℝ)^6285 := by
    have hnat : (5692292727 : ℕ)^8333*100000000000000^6285 ≤ 47374680381139^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5692292727 10000000000 47374680381139 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239731427/10000000000 : ℝ), (-178470941/1000000000 : ℝ), (5692292727/10000000000 : ℝ)] ![(42446746801053/100000000000000 : ℝ), (5089286407527/50000000000000 : ℝ), (47374680381139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239731427/10000000000 : ℝ)|^8333 ≤ (42446746801053/100000000000000 : ℝ)^6285
        have hw : |(5239731427/10000000000 : ℝ)|=(5239731427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178470941/1000000000 : ℝ)|^8333 ≤ (5089286407527/50000000000000 : ℝ)^6285
        have hw : |(-178470941/1000000000 : ℝ)|=(178470941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5692292727/10000000000 : ℝ)|^8333 ≤ (47374680381139/100000000000000 : ℝ)^6285
        have hw : |(5692292727/10000000000 : ℝ)|=(5692292727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239731487/10000000000 : ℝ)*x 0 + (142307323/250000000 : ℝ)*x 1 + (-1784709041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239731487/10000000000 : ℝ)^8333 ≤ (21223373722747/50000000000000 : ℝ)^6285 := by
    have hnat : (5239731487 : ℕ)^8333*50000000000000^6285 ≤ 21223373722747^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239731487 10000000000 21223373722747 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142307323/250000000 : ℝ)^8333 ≤ (4737468251081/10000000000000 : ℝ)^6285 := by
    have hnat : (142307323 : ℕ)^8333*10000000000000^6285 ≤ 4737468251081^6285*250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142307323 250000000 4737468251081 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1784709041/10000000000 : ℝ)^8333 ≤ (2544642506203/25000000000000 : ℝ)^6285 := by
    have hnat : (1784709041 : ℕ)^8333*25000000000000^6285 ≤ 2544642506203^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784709041 10000000000 2544642506203 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239731487/10000000000 : ℝ), (142307323/250000000 : ℝ), (-1784709041/10000000000 : ℝ)] ![(21223373722747/50000000000000 : ℝ), (4737468251081/10000000000000 : ℝ), (2544642506203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239731487/10000000000 : ℝ)|^8333 ≤ (21223373722747/50000000000000 : ℝ)^6285
        have hw : |(5239731487/10000000000 : ℝ)|=(5239731487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142307323/250000000 : ℝ)|^8333 ≤ (4737468251081/10000000000000 : ℝ)^6285
        have hw : |(142307323/250000000 : ℝ)|=(142307323/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1784709041/10000000000 : ℝ)|^8333 ≤ (2544642506203/25000000000000 : ℝ)^6285
        have hw : |(-1784709041/10000000000 : ℝ)|=(1784709041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s1_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2159605771/5000000000 : ℝ)*x 0 + (631264833/1250000000 : ℝ)*x 1 + (147842131/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159605771/5000000000 : ℝ)^8333 ≤ (4106852794661/12500000000000 : ℝ)^6285 := by
    have hnat : (2159605771 : ℕ)^8333*12500000000000^6285 ≤ 4106852794661^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159605771 5000000000 4106852794661 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631264833/1250000000 : ℝ)^8333 ≤ (40422284811417/100000000000000 : ℝ)^6285 := by
    have hnat : (631264833 : ℕ)^8333*100000000000000^6285 ≤ 40422284811417^6285*1250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631264833 1250000000 40422284811417 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147842131/400000000 : ℝ)^8333 ≤ (26722892825117/100000000000000 : ℝ)^6285 := by
    have hnat : (147842131 : ℕ)^8333*100000000000000^6285 ≤ 26722892825117^6285*400000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147842131 400000000 26722892825117 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159605771/5000000000 : ℝ), (631264833/1250000000 : ℝ), (147842131/400000000 : ℝ)] ![(4106852794661/12500000000000 : ℝ), (40422284811417/100000000000000 : ℝ), (26722892825117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159605771/5000000000 : ℝ)|^8333 ≤ (4106852794661/12500000000000 : ℝ)^6285
        have hw : |(2159605771/5000000000 : ℝ)|=(2159605771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(631264833/1250000000 : ℝ)|^8333 ≤ (40422284811417/100000000000000 : ℝ)^6285
        have hw : |(631264833/1250000000 : ℝ)|=(631264833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147842131/400000000 : ℝ)|^8333 ≤ (26722892825117/100000000000000 : ℝ)^6285
        have hw : |(147842131/400000000 : ℝ)|=(147842131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (81/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2819/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10223/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (81/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27823/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (81/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (81/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27823/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (81/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (81/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27823/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (81/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (81/20000 : ℝ) ^ (2083/512 : ℝ) ≤ (9230754867/50000000000000000000 : ℝ) := by
    have hpowers : (81/20000 : ℝ)^2083 ≤ (9230754867/50000000000000000000 : ℝ)^512 := by
      have hnat : (81 : ℕ)^2083*50000000000000000000^512 ≤ 9230754867^512*20000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81 20000 9230754867 50000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81/20000 : ℝ)) (X := (9230754867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27823/100000 : ℝ) ^ (2083/512 : ℝ) ≤ (549079999558466451/100000000000000000000 : ℝ) := by
    have hpowers : (27823/100000 : ℝ)^2083 ≤ (549079999558466451/100000000000000000000 : ℝ)^512 := by
      have hnat : (27823 : ℕ)^2083*100000000000000000000^512 ≤ 549079999558466451^512*100000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27823 100000 549079999558466451 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27823/100000 : ℝ)) (X := (549079999558466451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000009230754867/25000000000000000000 : ℝ) ≤ (5000000000453783/5000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (25000000009230754867/25000000000000000000 : ℝ)^512 ≤ (5000000000453783/5000000000000000 : ℝ)^2083 := by
      have hnat : (25000000009230754867 : ℕ)^512*5000000000000000^2083 ≤ 5000000000453783^2083*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000009230754867 25000000000000000000 5000000000453783 5000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000453783/5000000000000000 : ℝ)) (X := (25000000009230754867/25000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20109816003603995237/20000000000000000000 : ℝ) ≤ (10013468494016517/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (20109816003603995237/20000000000000000000 : ℝ)^512 ≤ (10013468494016517/10000000000000000 : ℝ)^2083 := by
      have hnat : (20109816003603995237 : ℕ)^512*10000000000000000^2083 ≤ 10013468494016517^2083*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20109816003603995237 20000000000000000000 10013468494016517 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013468494016517/10000000000000000 : ℝ)) (X := (20109816003603995237/20000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50549079999558466451/50000000000000000000 : ℝ) ≤ (2506734246781367/2500000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50549079999558466451/50000000000000000000 : ℝ)^512 ≤ (2506734246781367/2500000000000000 : ℝ)^2083 := by
      have hnat : (50549079999558466451 : ℕ)^512*2500000000000000^2083 ≤ 2506734246781367^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50549079999558466451 50000000000000000000 2506734246781367 2500000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506734246781367/2500000000000000 : ℝ)) (X := (50549079999558466451/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9230754867/50000000000000000000 : ℝ) ≤ ((137084545272732697139/137090000000000000000 : ℝ)+2*(13468493108951/2741800000000000 : ℝ)*(81/20000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (137084545272732697139/137090000000000000000 : ℝ)+2*(13468493108951/2741800000000000 : ℝ)*(81/20000 : ℝ)=(5000000000453783/5000000000000000 : ℝ) by norm_num, show 1+2*(9230754867/50000000000000000000 : ℝ)=(25000000009230754867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(549079999558466451/100000000000000000000 : ℝ)+(9230754867/50000000000000000000 : ℝ) ≤ ((137084545272732697139/137090000000000000000 : ℝ)+(13468493108951/2741800000000000 : ℝ)*((27823/100000 : ℝ)+(81/20000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (137084545272732697139/137090000000000000000 : ℝ)+(13468493108951/2741800000000000 : ℝ)*((27823/100000 : ℝ)+(81/20000 : ℝ))=(10013468494016517/10000000000000000 : ℝ) by norm_num, show 1+(549079999558466451/100000000000000000000 : ℝ)+(9230754867/50000000000000000000 : ℝ)=(20109816003603995237/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(549079999558466451/100000000000000000000 : ℝ) ≤ ((137084545272732697139/137090000000000000000 : ℝ)+2*(13468493108951/2741800000000000 : ℝ)*(27823/100000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (137084545272732697139/137090000000000000000 : ℝ)+2*(13468493108951/2741800000000000 : ℝ)*(27823/100000 : ℝ)=(2506734246781367/2500000000000000 : ℝ) by norm_num, show 1+2*(549079999558466451/100000000000000000000 : ℝ)=(50549079999558466451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137084545272732697139/137090000000000000000 : ℝ)*(X 1 0+X 2 0)+(13468493108951/2741800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (81/20000 : ℝ)) (hi := (27823/100000 : ℝ)) (c := (137084545272732697139/137090000000000000000 : ℝ)) (alpha := (13468493108951/2741800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137084545272732697139/137090000000000000000 : ℝ)*(X 0 1+X 2 1)+(13468493108951/2741800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (81/20000 : ℝ)) (hi := (27823/100000 : ℝ)) (c := (137084545272732697139/137090000000000000000 : ℝ)) (alpha := (13468493108951/2741800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137084545272732697139/137090000000000000000 : ℝ)*(X 0 2+X 1 2)+(13468493108951/2741800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (81/20000 : ℝ)) (hi := (27823/100000 : ℝ)) (c := (137084545272732697139/137090000000000000000 : ℝ)) (alpha := (13468493108951/2741800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419450089/2000000000 : ℝ)*X 0 0+(1140410201/2000000000 : ℝ)*X 0 1+(125046079/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709617053/5000000000 : ℝ)*X 1 0+(-123758011/500000000 : ℝ)*X 1 1+(5001842507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419236011/10000000000 : ℝ)*X 2 0+(5001840811/10000000000 : ℝ)*X 2 1+(-618789973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863521189/2000000000 : ℝ)*X 0 0+(229790563/625000000 : ℝ)*X 0 1+(5069145371/10000000000 : ℝ)*X 0 2+(863521189/2000000000 : ℝ)*X 1 0+(229790563/625000000 : ℝ)*X 1 1+(5069145371/10000000000 : ℝ)*X 1 2+(863521189/2000000000 : ℝ)*X 2 0+(229790563/625000000 : ℝ)*X 2 1+(5069145371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1049029897/5000000000 : ℝ)*X 0 0+(313213197/625000000 : ℝ)*X 0 1+(1423073263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239731427/10000000000 : ℝ)*X 1 0+(-178470941/1000000000 : ℝ)*X 1 1+(5692292727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239731487/10000000000 : ℝ)*X 2 0+(142307323/250000000 : ℝ)*X 2 1+(-1784709041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159605771/5000000000 : ℝ)*X 0 0+(631264833/1250000000 : ℝ)*X 0 1+(147842131/400000000 : ℝ)*X 0 2+(2159605771/5000000000 : ℝ)*X 1 0+(631264833/1250000000 : ℝ)*X 1 1+(147842131/400000000 : ℝ)*X 1 2+(2159605771/5000000000 : ℝ)*X 2 0+(631264833/1250000000 : ℝ)*X 2 1+(147842131/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (936391555997923704740343/137090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529356303/100000000000000 : ℝ)*(base1) + (1102989071/100000000000000 : ℝ)*(base19) + (1625932677/100000000000000 : ℝ)*(base23) + (52829/12500000000000 : ℝ)*(upper3) + (1175099/781250000000 : ℝ)*(upper5) + (1073143363080037/100000000000000 : ℝ)*(major0) + (1073143363080037/100000000000000 : ℝ)*(major1) + (1073143363080037/100000000000000 : ℝ)*(major2) + (1428148219756673/100000000000000 : ℝ)*(sp0) + (17851867253703/1250000000000 : ℝ)*(sp1) + (1428149488702803/100000000000000 : ℝ)*(sp2) + (8976685681067/1250000000000 : ℝ)*(sp3) + (3424235109/100000000000000 : ℝ)*(sp4) + (78918771/12500000000000 : ℝ)*(sp5) + (359067691920831/50000000000000 : ℝ)*(f.failure) + (35703777865887/2500000000000 : ℝ)*(f.sum) + (163581299977023/137090000000000000000000000000 : ℝ)*base66 + (33631064329480264143/13709000000000000000000000000000000 : ℝ)*base67 + (108691292129874735857/13709000000000000000000000000000000 : ℝ)*base70 + (26422987792313264143/13709000000000000000000000000000000 : ℝ)*base71 + (119970370516813/137090000000000000000000000000 : ℝ)*base74 + (29819886066313264143/13709000000000000000000000000000000 : ℝ)*base75 + (11843597237499735857/13709000000000000000000000000000000 : ℝ)*base78 + (8151929142219735857/13709000000000000000000000000000000 : ℝ)*base80 + (646590924012373/137090000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (40735103/5000000000000000000000 : ℝ)*base90 + (40735103/5000000000000000000000 : ℝ)*base92 + (40735103/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (322781934963860746799991/137090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19573607/50000000000000 : ℝ)*(base1) + (544557217/100000000000000 : ℝ)*(base19) + (585827751/100000000000000 : ℝ)*(base23) + (35264807/100000000000000 : ℝ)*(upper3) + (23950797/50000000000000 : ℝ)*(upper5) + (1103600281051373/100000000000000 : ℝ)*(major0) + (1103600281051373/100000000000000 : ℝ)*(major1) + (1103600281051373/100000000000000 : ℝ)*(major2) + (936334987/50000000000000 : ℝ)*(sp1) + (2586424001/100000000000000 : ℝ)*(sp2) + (183585464297691/12500000000000 : ℝ)*(sp4) + (1468681258007123/100000000000000 : ℝ)*(sp5) + (1468680502982561/100000000000000 : ℝ)*(sp6) + (369258384618511/50000000000000 : ℝ)*(sp7) + (184629202096059/25000000000000 : ℝ)*(f.failure) + (1468683675234313/100000000000000 : ℝ)*(f.sum) + (82985863706557/137090000000000000000000000000 : ℝ)*base66 + (2131321096680728153/13709000000000000000000000000000000 : ℝ)*base68 + (22382953103141271847/13709000000000000000000000000000000 : ℝ)*base69 + (10138978650605728153/13709000000000000000000000000000000 : ℝ)*base72 + (155469276592903/137090000000000000000000000000 : ℝ)*base73 + (114588269146005728153/13709000000000000000000000000000000 : ℝ)*base76 + (16434403649217271847/13709000000000000000000000000000000 : ℝ)*base77 + (115581382001744271847/13709000000000000000000000000000000 : ℝ)*base79 + (346390645566593/137090000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4401467/2500000000000000000000 : ℝ)*base90 + (4401467/2500000000000000000000 : ℝ)*base92 + (4401467/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1140_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27823/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (81/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10223/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s2_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150595377/10000000000 : ℝ)*x 0 + (551118779/1000000000 : ℝ)*x 1 + (5158787127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150595377/10000000000 : ℝ)^8333 ≤ (6516876476477/50000000000000 : ℝ)^6285 := by
    have hnat : (2150595377 : ℕ)^8333*50000000000000^6285 ≤ 6516876476477^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150595377 10000000000 6516876476477 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551118779/1000000000 : ℝ)^8333 ≤ (4538670060639/10000000000000 : ℝ)^6285 := by
    have hnat : (551118779 : ℕ)^8333*10000000000000^6285 ≤ 4538670060639^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551118779 1000000000 4538670060639 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5158787127/10000000000 : ℝ)^8333 ≤ (41579546424909/100000000000000 : ℝ)^6285 := by
    have hnat : (5158787127 : ℕ)^8333*100000000000000^6285 ≤ 41579546424909^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158787127 10000000000 41579546424909 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150595377/10000000000 : ℝ), (551118779/1000000000 : ℝ), (5158787127/10000000000 : ℝ)] ![(6516876476477/50000000000000 : ℝ), (4538670060639/10000000000000 : ℝ), (41579546424909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150595377/10000000000 : ℝ)|^8333 ≤ (6516876476477/50000000000000 : ℝ)^6285
        have hw : |(-2150595377/10000000000 : ℝ)|=(2150595377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551118779/1000000000 : ℝ)|^8333 ≤ (4538670060639/10000000000000 : ℝ)^6285
        have hw : |(551118779/1000000000 : ℝ)|=(551118779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5158787127/10000000000 : ℝ)|^8333 ≤ (41579546424909/100000000000000 : ℝ)^6285
        have hw : |(5158787127/10000000000 : ℝ)|=(5158787127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373948983/10000000000 : ℝ)*x 0 + (-1166911443/5000000000 : ℝ)*x 1 + (2579394557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373948983/10000000000 : ℝ)^8333 ≤ (2743394735401/6250000000000 : ℝ)^6285 := by
    have hnat : (5373948983 : ℕ)^8333*6250000000000^6285 ≤ 2743394735401^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373948983 10000000000 2743394735401 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166911443/5000000000 : ℝ)^8333 ≤ (290522331271/2000000000000 : ℝ)^6285 := by
    have hnat : (1166911443 : ℕ)^8333*2000000000000^6285 ≤ 290522331271^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166911443 5000000000 290522331271 2000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579394557/5000000000 : ℝ)^8333 ≤ (41579567658631/100000000000000 : ℝ)^6285 := by
    have hnat : (2579394557 : ℕ)^8333*100000000000000^6285 ≤ 41579567658631^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579394557 5000000000 41579567658631 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373948983/10000000000 : ℝ), (-1166911443/5000000000 : ℝ), (2579394557/5000000000 : ℝ)] ![(2743394735401/6250000000000 : ℝ), (290522331271/2000000000000 : ℝ), (41579567658631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373948983/10000000000 : ℝ)|^8333 ≤ (2743394735401/6250000000000 : ℝ)^6285
        have hw : |(5373948983/10000000000 : ℝ)|=(5373948983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1166911443/5000000000 : ℝ)|^8333 ≤ (290522331271/2000000000000 : ℝ)^6285
        have hw : |(-1166911443/5000000000 : ℝ)|=(1166911443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579394557/5000000000 : ℝ)|^8333 ≤ (41579567658631/100000000000000 : ℝ)^6285
        have hw : |(2579394557/5000000000 : ℝ)|=(2579394557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686974481/5000000000 : ℝ)*x 0 + (2579394501/5000000000 : ℝ)*x 1 + (-1166911529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686974481/5000000000 : ℝ)^8333 ≤ (8778863107799/20000000000000 : ℝ)^6285 := by
    have hnat : (2686974481 : ℕ)^8333*20000000000000^6285 ≤ 8778863107799^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686974481 5000000000 8778863107799 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579394501/5000000000 : ℝ)^8333 ≤ (41579566461763/100000000000000 : ℝ)^6285 := by
    have hnat : (2579394501 : ℕ)^8333*100000000000000^6285 ≤ 41579566461763^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579394501 5000000000 41579566461763 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166911529/5000000000 : ℝ)^8333 ≤ (2905223596591/20000000000000 : ℝ)^6285 := by
    have hnat : (1166911529 : ℕ)^8333*20000000000000^6285 ≤ 2905223596591^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166911529 5000000000 2905223596591 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686974481/5000000000 : ℝ), (2579394501/5000000000 : ℝ), (-1166911529/5000000000 : ℝ)] ![(8778863107799/20000000000000 : ℝ), (41579566461763/100000000000000 : ℝ), (2905223596591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686974481/5000000000 : ℝ)|^8333 ≤ (8778863107799/20000000000000 : ℝ)^6285
        have hw : |(2686974481/5000000000 : ℝ)|=(2686974481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2579394501/5000000000 : ℝ)|^8333 ≤ (41579566461763/100000000000000 : ℝ)^6285
        have hw : |(2579394501/5000000000 : ℝ)|=(2579394501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1166911529/5000000000 : ℝ)|^8333 ≤ (2905223596591/20000000000000 : ℝ)^6285
        have hw : |(-1166911529/5000000000 : ℝ)|=(1166911529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088549117/2500000000 : ℝ)*x 0 + (803553913/2000000000 : ℝ)*x 1 + (943716379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088549117/2500000000 : ℝ)^8333 ≤ (8302030546057/25000000000000 : ℝ)^6285 := by
    have hnat : (1088549117 : ℕ)^8333*25000000000000^6285 ≤ 8302030546057^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088549117 2500000000 8302030546057 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803553913/2000000000 : ℝ)^8333 ≤ (29849803829517/100000000000000 : ℝ)^6285 := by
    have hnat : (803553913 : ℕ)^8333*100000000000000^6285 ≤ 29849803829517^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803553913 2000000000 29849803829517 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943716379/2000000000 : ℝ)^8333 ≤ (9235518492791/25000000000000 : ℝ)^6285 := by
    have hnat : (943716379 : ℕ)^8333*25000000000000^6285 ≤ 9235518492791^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943716379 2000000000 9235518492791 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088549117/2500000000 : ℝ), (803553913/2000000000 : ℝ), (943716379/2000000000 : ℝ)] ![(8302030546057/25000000000000 : ℝ), (29849803829517/100000000000000 : ℝ), (9235518492791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088549117/2500000000 : ℝ)|^8333 ≤ (8302030546057/25000000000000 : ℝ)^6285
        have hw : |(1088549117/2500000000 : ℝ)|=(1088549117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803553913/2000000000 : ℝ)|^8333 ≤ (29849803829517/100000000000000 : ℝ)^6285
        have hw : |(803553913/2000000000 : ℝ)|=(803553913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943716379/2000000000 : ℝ)|^8333 ≤ (9235518492791/25000000000000 : ℝ)^6285
        have hw : |(943716379/2000000000 : ℝ)|=(943716379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86027943/400000000 : ℝ)*x 0 + (2580610353/5000000000 : ℝ)*x 1 + (344295609/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86027943/400000000 : ℝ)^8333 ≤ (2606916439091/20000000000000 : ℝ)^6285 := by
    have hnat : (86027943 : ℕ)^8333*20000000000000^6285 ≤ 2606916439091^6285*400000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86027943 400000000 2606916439091 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580610353/5000000000 : ℝ)^8333 ≤ (41605554431309/100000000000000 : ℝ)^6285 := by
    have hnat : (2580610353 : ℕ)^8333*100000000000000^6285 ≤ 41605554431309^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580610353 5000000000 41605554431309 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344295609/625000000 : ℝ)^8333 ≤ (11339965840119/25000000000000 : ℝ)^6285 := by
    have hnat : (344295609 : ℕ)^8333*25000000000000^6285 ≤ 11339965840119^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344295609 625000000 11339965840119 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86027943/400000000 : ℝ), (2580610353/5000000000 : ℝ), (344295609/625000000 : ℝ)] ![(2606916439091/20000000000000 : ℝ), (41605554431309/100000000000000 : ℝ), (11339965840119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86027943/400000000 : ℝ)|^8333 ≤ (2606916439091/20000000000000 : ℝ)^6285
        have hw : |(-86027943/400000000 : ℝ)|=(86027943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2580610353/5000000000 : ℝ)|^8333 ≤ (41605554431309/100000000000000 : ℝ)^6285
        have hw : |(2580610353/5000000000 : ℝ)|=(2580610353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(344295609/625000000 : ℝ)|^8333 ≤ (11339965840119/25000000000000 : ℝ)^6285
        have hw : |(344295609/625000000 : ℝ)|=(344295609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321136919/2500000000 : ℝ)*x 0 + (-1983880237/10000000000 : ℝ)*x 1 + (2754365201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321136919/2500000000 : ℝ)^8333 ≤ (42928772972087/100000000000000 : ℝ)^6285 := by
    have hnat : (1321136919 : ℕ)^8333*100000000000000^6285 ≤ 42928772972087^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321136919 2500000000 42928772972087 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983880237/10000000000 : ℝ)^8333 ≤ (11711356472429/100000000000000 : ℝ)^6285 := by
    have hnat : (1983880237 : ℕ)^8333*100000000000000^6285 ≤ 11711356472429^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983880237 10000000000 11711356472429 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754365201/5000000000 : ℝ)^8333 ≤ (45359870544079/100000000000000 : ℝ)^6285 := by
    have hnat : (2754365201 : ℕ)^8333*100000000000000^6285 ≤ 45359870544079^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754365201 5000000000 45359870544079 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321136919/2500000000 : ℝ), (-1983880237/10000000000 : ℝ), (2754365201/5000000000 : ℝ)] ![(42928772972087/100000000000000 : ℝ), (11711356472429/100000000000000 : ℝ), (45359870544079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321136919/2500000000 : ℝ)|^8333 ≤ (42928772972087/100000000000000 : ℝ)^6285
        have hw : |(1321136919/2500000000 : ℝ)|=(1321136919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1983880237/10000000000 : ℝ)|^8333 ≤ (11711356472429/100000000000000 : ℝ)^6285
        have hw : |(-1983880237/10000000000 : ℝ)|=(1983880237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754365201/5000000000 : ℝ)|^8333 ≤ (45359870544079/100000000000000 : ℝ)^6285
        have hw : |(2754365201/5000000000 : ℝ)|=(2754365201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284546209/10000000000 : ℝ)*x 0 + (5508730207/10000000000 : ℝ)*x 1 + (-1983882527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284546209/10000000000 : ℝ)^8333 ≤ (10732189292933/25000000000000 : ℝ)^6285 := by
    have hnat : (5284546209 : ℕ)^8333*25000000000000^6285 ≤ 10732189292933^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284546209 10000000000 10732189292933 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508730207/10000000000 : ℝ)^8333 ≤ (45359868415199/100000000000000 : ℝ)^6285 := by
    have hnat : (5508730207 : ℕ)^8333*100000000000000^6285 ≤ 45359868415199^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508730207 10000000000 45359868415199 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983882527/10000000000 : ℝ)^8333 ≤ (11711374395953/100000000000000 : ℝ)^6285 := by
    have hnat : (1983882527 : ℕ)^8333*100000000000000^6285 ≤ 11711374395953^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983882527 10000000000 11711374395953 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284546209/10000000000 : ℝ), (5508730207/10000000000 : ℝ), (-1983882527/10000000000 : ℝ)] ![(10732189292933/25000000000000 : ℝ), (45359868415199/100000000000000 : ℝ), (11711374395953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284546209/10000000000 : ℝ)|^8333 ≤ (10732189292933/25000000000000 : ℝ)^6285
        have hw : |(5284546209/10000000000 : ℝ)|=(5284546209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508730207/10000000000 : ℝ)|^8333 ≤ (45359868415199/100000000000000 : ℝ)^6285
        have hw : |(5508730207/10000000000 : ℝ)|=(5508730207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983882527/10000000000 : ℝ)|^8333 ≤ (11711374395953/100000000000000 : ℝ)^6285
        have hw : |(-1983882527/10000000000 : ℝ)|=(1983882527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s2_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354400873/10000000000 : ℝ)*x 0 + (2356871973/5000000000 : ℝ)*x 1 + (804531217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354400873/10000000000 : ℝ)^8333 ≤ (33210189121199/100000000000000 : ℝ)^6285 := by
    have hnat : (4354400873 : ℕ)^8333*100000000000000^6285 ≤ 33210189121199^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354400873 10000000000 33210189121199 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2356871973/5000000000 : ℝ)^8333 ≤ (36891863465987/100000000000000 : ℝ)^6285 := by
    have hnat : (2356871973 : ℕ)^8333*100000000000000^6285 ≤ 36891863465987^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356871973 5000000000 36891863465987 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804531217/2000000000 : ℝ)^8333 ≤ (29897947396427/100000000000000 : ℝ)^6285 := by
    have hnat : (804531217 : ℕ)^8333*100000000000000^6285 ≤ 29897947396427^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804531217 2000000000 29897947396427 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354400873/10000000000 : ℝ), (2356871973/5000000000 : ℝ), (804531217/2000000000 : ℝ)] ![(33210189121199/100000000000000 : ℝ), (36891863465987/100000000000000 : ℝ), (29897947396427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354400873/10000000000 : ℝ)|^8333 ≤ (33210189121199/100000000000000 : ℝ)^6285
        have hw : |(4354400873/10000000000 : ℝ)|=(4354400873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2356871973/5000000000 : ℝ)|^8333 ≤ (36891863465987/100000000000000 : ℝ)^6285
        have hw : |(2356871973/5000000000 : ℝ)|=(2356871973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804531217/2000000000 : ℝ)|^8333 ≤ (29897947396427/100000000000000 : ℝ)^6285
        have hw : |(804531217/2000000000 : ℝ)|=(804531217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4127/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10223/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10223/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10223/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/50000 : ℝ) ^ (2083/512 : ℝ) ≤ (207523835363103/25000000000000000000 : ℝ) := by
    have hpowers : (2819/50000 : ℝ)^2083 ≤ (207523835363103/25000000000000000000 : ℝ)^512 := by
      have hnat : (2819 : ℕ)^2083*25000000000000000000^512 ≤ 207523835363103^512*50000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 50000 207523835363103 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/50000 : ℝ)) (X := (207523835363103/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10223/50000 : ℝ) ^ (2083/512 : ℝ) ≤ (156785914666333667/100000000000000000000 : ℝ) := by
    have hpowers : (10223/50000 : ℝ)^2083 ≤ (156785914666333667/100000000000000000000 : ℝ)^512 := by
      have hnat : (10223 : ℕ)^2083*100000000000000000000^512 ≤ 156785914666333667^512*50000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10223 50000 156785914666333667 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10223/50000 : ℝ)) (X := (156785914666333667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500207523835363103/12500000000000000000 : ℝ) ≤ (1250005100889991/1250000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (12500207523835363103/12500000000000000000 : ℝ)^512 ≤ (1250005100889991/1250000000000000 : ℝ)^2083 := by
      have hnat : (12500207523835363103 : ℕ)^512*1250000000000000^2083 ≤ 1250005100889991^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500207523835363103 12500000000000000000 1250005100889991 1250000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005100889991/1250000000000000 : ℝ)) (X := (12500207523835363103/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100157616010007786079/100000000000000000000 : ℝ) ≤ (2500967972586909/2500000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (100157616010007786079/100000000000000000000 : ℝ)^512 ≤ (2500967972586909/2500000000000000 : ℝ)^2083 := by
      have hnat : (100157616010007786079 : ℕ)^512*2500000000000000^2083 ≤ 2500967972586909^2083*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100157616010007786079 100000000000000000000 2500967972586909 2500000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500967972586909/2500000000000000 : ℝ)) (X := (100157616010007786079/100000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50156785914666333667/50000000000000000000 : ℝ) ≤ (625481435848459/625000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50156785914666333667/50000000000000000000 : ℝ)^512 ≤ (625481435848459/625000000000000 : ℝ)^2083 := by
      have hnat : (50156785914666333667 : ℕ)^512*625000000000000^2083 ≤ 625481435848459^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50156785914666333667 50000000000000000000 625481435848459 625000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625481435848459/625000000000000 : ℝ)) (X := (50156785914666333667/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(207523835363103/25000000000000000000 : ℝ) ≤ ((9252337811084766151/9255000000000000000 : ℝ)+2*(957770806927/370200000000000 : ℝ)*(2819/50000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (9252337811084766151/9255000000000000000 : ℝ)+2*(957770806927/370200000000000 : ℝ)*(2819/50000 : ℝ)=(1250005100889991/1250000000000000 : ℝ) by norm_num, show 1+2*(207523835363103/25000000000000000000 : ℝ)=(12500207523835363103/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(156785914666333667/100000000000000000000 : ℝ)+(207523835363103/25000000000000000000 : ℝ) ≤ ((9252337811084766151/9255000000000000000 : ℝ)+(957770806927/370200000000000 : ℝ)*((10223/50000 : ℝ)+(2819/50000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (9252337811084766151/9255000000000000000 : ℝ)+(957770806927/370200000000000 : ℝ)*((10223/50000 : ℝ)+(2819/50000 : ℝ))=(2500967972586909/2500000000000000 : ℝ) by norm_num, show 1+(156785914666333667/100000000000000000000 : ℝ)+(207523835363103/25000000000000000000 : ℝ)=(100157616010007786079/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(156785914666333667/100000000000000000000 : ℝ) ≤ ((9252337811084766151/9255000000000000000 : ℝ)+2*(957770806927/370200000000000 : ℝ)*(10223/50000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (9252337811084766151/9255000000000000000 : ℝ)+2*(957770806927/370200000000000 : ℝ)*(10223/50000 : ℝ)=(625481435848459/625000000000000 : ℝ) by norm_num, show 1+2*(156785914666333667/100000000000000000000 : ℝ)=(50156785914666333667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9252337811084766151/9255000000000000000 : ℝ)*(X 1 0+X 2 0)+(957770806927/370200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2819/50000 : ℝ)) (hi := (10223/50000 : ℝ)) (c := (9252337811084766151/9255000000000000000 : ℝ)) (alpha := (957770806927/370200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9252337811084766151/9255000000000000000 : ℝ)*(X 0 1+X 2 1)+(957770806927/370200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2819/50000 : ℝ)) (hi := (10223/50000 : ℝ)) (c := (9252337811084766151/9255000000000000000 : ℝ)) (alpha := (957770806927/370200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9252337811084766151/9255000000000000000 : ℝ)*(X 0 2+X 1 2)+(957770806927/370200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (2819/50000 : ℝ)) (hi := (10223/50000 : ℝ)) (c := (9252337811084766151/9255000000000000000 : ℝ)) (alpha := (957770806927/370200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150595377/10000000000 : ℝ)*X 0 0+(551118779/1000000000 : ℝ)*X 0 1+(5158787127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373948983/10000000000 : ℝ)*X 1 0+(-1166911443/5000000000 : ℝ)*X 1 1+(2579394557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686974481/5000000000 : ℝ)*X 2 0+(2579394501/5000000000 : ℝ)*X 2 1+(-1166911529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088549117/2500000000 : ℝ)*X 0 0+(803553913/2000000000 : ℝ)*X 0 1+(943716379/2000000000 : ℝ)*X 0 2+(1088549117/2500000000 : ℝ)*X 1 0+(803553913/2000000000 : ℝ)*X 1 1+(943716379/2000000000 : ℝ)*X 1 2+(1088549117/2500000000 : ℝ)*X 2 0+(803553913/2000000000 : ℝ)*X 2 1+(943716379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86027943/400000000 : ℝ)*X 0 0+(2580610353/5000000000 : ℝ)*X 0 1+(344295609/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321136919/2500000000 : ℝ)*X 1 0+(-1983880237/10000000000 : ℝ)*X 1 1+(2754365201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284546209/10000000000 : ℝ)*X 2 0+(5508730207/10000000000 : ℝ)*X 2 1+(-1983882527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354400873/10000000000 : ℝ)*X 0 0+(2356871973/5000000000 : ℝ)*X 0 1+(804531217/2000000000 : ℝ)*X 0 2+(4354400873/10000000000 : ℝ)*X 1 0+(2356871973/5000000000 : ℝ)*X 1 1+(804531217/2000000000 : ℝ)*X 1 2+(4354400873/10000000000 : ℝ)*X 2 0+(2356871973/5000000000 : ℝ)*X 2 1+(804531217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28380139432794780323577/3085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (958107363/100000000000000 : ℝ)*(base19) + (328692653/50000000000000 : ℝ)*(base23) + (2409769/20000000000000 : ℝ)*(upper2) + (166262389/50000000000000 : ℝ)*(upper3) + (167696127/100000000000000 : ℝ)*(upper4) + (533081440427369/25000000000000 : ℝ)*(major0) + (533081440427369/25000000000000 : ℝ)*(major1) + (533081440427369/25000000000000 : ℝ)*(major2) + (1418851551547479/50000000000000 : ℝ)*(sp0) + (709430502566531/25000000000000 : ℝ)*(sp1) + (2837722310988181/100000000000000 : ℝ)*(sp2) + (142692031260663/10000000000000 : ℝ)*(sp3) + (19865278529/100000000000000 : ℝ)*(sp4) + (1983948067/25000000000000 : ℝ)*(sp7) + (713464124199449/50000000000000 : ℝ)*(f.failure) + (2837722968373487/100000000000000 : ℝ)*(f.sum) + (88265577000061/9255000000000000000000000000 : ℝ)*base65 + (1127667573504738281/231375000000000000000000000000000 : ℝ)*base68 + (178238100017238281/231375000000000000000000000000000 : ℝ)*base70 + (200847203454761719/231375000000000000000000000000000 : ℝ)*base71 + (3306314545639/2313750000000000000000000000 : ℝ)*base73 + (284904799258511719/231375000000000000000000000000000 : ℝ)*base75 + (689961870511488281/231375000000000000000000000000000 : ℝ)*base78 + (301628104386761719/231375000000000000000000000000000 : ℝ)*base79 + (4438974256733/4627500000000000000000000000 : ℝ)*base81 + (13112537/5000000000000000000000 : ℝ)*base90 + (13112537/5000000000000000000000 : ℝ)*base92 + (13112537/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273678560803877671402397049/77125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4051213/1000000000000 : ℝ)*(base19) + (4149223/12500000000000 : ℝ)*(base23) + (10714647/3125000000000 : ℝ)*(upper2) + (13573363/10000000000000 : ℝ)*(upper3) + (2162308982320699/100000000000000 : ℝ)*(major0) + (2162308982320699/100000000000000 : ℝ)*(major1) + (2162308982320699/100000000000000 : ℝ)*(major2) + (6385448277/100000000000000 : ℝ)*(sp0) + (3279257603/25000000000000 : ℝ)*(sp1) + (327755843/100000000000000 : ℝ)*(sp3) + (2302095024701/80000000000 : ℝ)*(sp4) + (179850727760801/6250000000000 : ℝ)*(sp5) + (2877625133130743/100000000000000 : ℝ)*(sp6) + (723496176138737/50000000000000 : ℝ)*(sp7) + (1446992680033317/100000000000000 : ℝ)*(f.failure) + (2877625166324527/100000000000000 : ℝ)*(f.sum) + (17118362581003/18510000000000000000000000000 : ℝ)*base65 + (489192026411684549/925500000000000000000000000000000 : ℝ)*base67 + (1530934699675815451/925500000000000000000000000000000 : ℝ)*base70 + (8137655305867815451/925500000000000000000000000000000 : ℝ)*base72 + (57623682151723/18510000000000000000000000000 : ℝ)*base73 + (7827645047511315451/925500000000000000000000000000000 : ℝ)*base76 + (677529908580315451/925500000000000000000000000000000 : ℝ)*base78 + (3436671125998815451/925500000000000000000000000000000 : ℝ)*base80 + (52200218919167/18510000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (24533221/10000000000000000000000 : ℝ)*base90 + (24533221/10000000000000000000000 : ℝ)*base92 + (24533221/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1140_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10223/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1140_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1140_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1140_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1140_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4127/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
