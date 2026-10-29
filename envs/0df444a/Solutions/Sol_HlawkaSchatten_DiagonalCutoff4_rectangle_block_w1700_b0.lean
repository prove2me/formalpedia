-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1700_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:22.157505+00:00
-- url     : https://prove2.me/submissions/7d0dce8d-6bf5-4612-913b-bed1d3321db7

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
theorem support_rectangle_w1700_s0_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1366557933/10000000000 : ℝ)*x 0 + (228732371/400000000 : ℝ)*x 1 + (4949335133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1366557933/10000000000 : ℝ)^5223 ≤ (841076976591/10000000000000 : ℝ)^4199 := by
    have hnat : (1366557933 : ℕ)^5223*10000000000000^4199 ≤ 841076976591^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366557933 10000000000 841076976591 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228732371/400000000 : ℝ)^5223 ≤ (12474211241691/25000000000000 : ℝ)^4199 := by
    have hnat : (228732371 : ℕ)^5223*25000000000000^4199 ≤ 12474211241691^4199*400000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228732371 400000000 12474211241691 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4949335133/10000000000 : ℝ)^5223 ≤ (41692385259851/100000000000000 : ℝ)^4199 := by
    have hnat : (4949335133 : ℕ)^5223*100000000000000^4199 ≤ 41692385259851^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949335133 10000000000 41692385259851 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1366557933/10000000000 : ℝ), (228732371/400000000 : ℝ), (4949335133/10000000000 : ℝ)] ![(841076976591/10000000000000 : ℝ), (12474211241691/25000000000000 : ℝ), (41692385259851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1366557933/10000000000 : ℝ)|^5223 ≤ (841076976591/10000000000000 : ℝ)^4199
        have hw : |(-1366557933/10000000000 : ℝ)|=(1366557933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228732371/400000000 : ℝ)|^5223 ≤ (12474211241691/25000000000000 : ℝ)^4199
        have hw : |(228732371/400000000 : ℝ)|=(228732371/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4949335133/10000000000 : ℝ)|^5223 ≤ (41692385259851/100000000000000 : ℝ)^4199
        have hw : |(4949335133/10000000000 : ℝ)|=(4949335133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411350423/10000000000 : ℝ)*x 0 + (-178434727/1000000000 : ℝ)*x 1 + (9666669/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411350423/10000000000 : ℝ)^5223 ≤ (46587301229011/100000000000000 : ℝ)^4199 := by
    have hnat : (5411350423 : ℕ)^5223*100000000000000^4199 ≤ 46587301229011^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411350423 10000000000 46587301229011 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178434727/1000000000 : ℝ)^5223 ≤ (732519989409/6250000000000 : ℝ)^4199 := by
    have hnat : (178434727 : ℕ)^5223*6250000000000^4199 ≤ 732519989409^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178434727 1000000000 732519989409 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9666669/19531250 : ℝ)^5223 ≤ (20846189460289/50000000000000 : ℝ)^4199 := by
    have hnat : (9666669 : ℕ)^5223*50000000000000^4199 ≤ 20846189460289^4199*19531250^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9666669 19531250 20846189460289 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411350423/10000000000 : ℝ), (-178434727/1000000000 : ℝ), (9666669/19531250 : ℝ)] ![(46587301229011/100000000000000 : ℝ), (732519989409/6250000000000 : ℝ), (20846189460289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411350423/10000000000 : ℝ)|^5223 ≤ (46587301229011/100000000000000 : ℝ)^4199
        have hw : |(5411350423/10000000000 : ℝ)|=(5411350423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178434727/1000000000 : ℝ)|^5223 ≤ (732519989409/6250000000000 : ℝ)^4199
        have hw : |(-178434727/1000000000 : ℝ)|=(178434727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9666669/19531250 : ℝ)|^5223 ≤ (20846189460289/50000000000000 : ℝ)^4199
        have hw : |(9666669/19531250 : ℝ)|=(9666669/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411349753/10000000000 : ℝ)*x 0 + (4949335143/10000000000 : ℝ)*x 1 + (-11152171/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411349753/10000000000 : ℝ)^5223 ≤ (23293647027097/50000000000000 : ℝ)^4199 := by
    have hnat : (5411349753 : ℕ)^5223*50000000000000^4199 ≤ 23293647027097^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411349753 10000000000 23293647027097 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4949335143/10000000000 : ℝ)^5223 ≤ (5211548170579/12500000000000 : ℝ)^4199 := by
    have hnat : (4949335143 : ℕ)^5223*12500000000000^4199 ≤ 5211548170579^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949335143 10000000000 5211548170579 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11152171/62500000 : ℝ)^5223 ≤ (2344064113173/20000000000000 : ℝ)^4199 := by
    have hnat : (11152171 : ℕ)^5223*20000000000000^4199 ≤ 2344064113173^4199*62500000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11152171 62500000 2344064113173 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411349753/10000000000 : ℝ), (4949335143/10000000000 : ℝ), (-11152171/62500000 : ℝ)] ![(23293647027097/50000000000000 : ℝ), (5211548170579/12500000000000 : ℝ), (2344064113173/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411349753/10000000000 : ℝ)|^5223 ≤ (23293647027097/50000000000000 : ℝ)^4199
        have hw : |(5411349753/10000000000 : ℝ)|=(5411349753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4949335143/10000000000 : ℝ)|^5223 ≤ (5211548170579/12500000000000 : ℝ)^4199
        have hw : |(4949335143/10000000000 : ℝ)|=(4949335143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11152171/62500000 : ℝ)|^5223 ≤ (2344064113173/20000000000000 : ℝ)^4199
        have hw : |(-11152171/62500000 : ℝ)|=(11152171/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1012007029/2500000000 : ℝ)*x 0 + (305305557/1000000000 : ℝ)*x 1 + (2615850293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012007029/2500000000 : ℝ)^5223 ≤ (16234276906861/50000000000000 : ℝ)^4199 := by
    have hnat : (1012007029 : ℕ)^5223*50000000000000^4199 ≤ 16234276906861^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012007029 2500000000 16234276906861 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305305557/1000000000 : ℝ)^5223 ≤ (914404168201/4000000000000 : ℝ)^4199 := by
    have hnat : (305305557 : ℕ)^5223*4000000000000^4199 ≤ 914404168201^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305305557 1000000000 914404168201 4000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615850293/5000000000 : ℝ)^5223 ≤ (44671341961507/100000000000000 : ℝ)^4199 := by
    have hnat : (2615850293 : ℕ)^5223*100000000000000^4199 ≤ 44671341961507^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615850293 5000000000 44671341961507 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1012007029/2500000000 : ℝ), (305305557/1000000000 : ℝ), (2615850293/5000000000 : ℝ)] ![(16234276906861/50000000000000 : ℝ), (914404168201/4000000000000 : ℝ), (44671341961507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1012007029/2500000000 : ℝ)|^5223 ≤ (16234276906861/50000000000000 : ℝ)^4199
        have hw : |(1012007029/2500000000 : ℝ)|=(1012007029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305305557/1000000000 : ℝ)|^5223 ≤ (914404168201/4000000000000 : ℝ)^4199
        have hw : |(305305557/1000000000 : ℝ)|=(305305557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615850293/5000000000 : ℝ)|^5223 ≤ (44671341961507/100000000000000 : ℝ)^4199
        have hw : |(2615850293/5000000000 : ℝ)|=(2615850293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1368389863/10000000000 : ℝ)*x 0 + (993687321/2000000000 : ℝ)*x 1 + (1139711897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368389863/10000000000 : ℝ)^5223 ≤ (8424796665307/100000000000000 : ℝ)^4199 := by
    have hnat : (1368389863 : ℕ)^5223*100000000000000^4199 ≤ 8424796665307^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368389863 10000000000 8424796665307 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993687321/2000000000 : ℝ)^5223 ≤ (2618289198613/6250000000000 : ℝ)^4199 := by
    have hnat : (993687321 : ℕ)^5223*6250000000000^4199 ≤ 2618289198613^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993687321 2000000000 2618289198613 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139711897/2000000000 : ℝ)^5223 ≤ (49682576143387/100000000000000 : ℝ)^4199 := by
    have hnat : (1139711897 : ℕ)^5223*100000000000000^4199 ≤ 49682576143387^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139711897 2000000000 49682576143387 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1368389863/10000000000 : ℝ), (993687321/2000000000 : ℝ), (1139711897/2000000000 : ℝ)] ![(8424796665307/100000000000000 : ℝ), (2618289198613/6250000000000 : ℝ), (49682576143387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1368389863/10000000000 : ℝ)|^5223 ≤ (8424796665307/100000000000000 : ℝ)^4199
        have hw : |(-1368389863/10000000000 : ℝ)|=(1368389863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993687321/2000000000 : ℝ)|^5223 ≤ (2618289198613/6250000000000 : ℝ)^4199
        have hw : |(993687321/2000000000 : ℝ)|=(993687321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139711897/2000000000 : ℝ)|^5223 ≤ (49682576143387/100000000000000 : ℝ)^4199
        have hw : |(1139711897/2000000000 : ℝ)|=(1139711897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202726143/10000000000 : ℝ)*x 0 + (-16173793/156250000 : ℝ)*x 1 + (712319923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202726143/10000000000 : ℝ)^5223 ≤ (2218190807373/5000000000000 : ℝ)^4199 := by
    have hnat : (5202726143 : ℕ)^5223*5000000000000^4199 ≤ 2218190807373^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202726143 10000000000 2218190807373 5000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16173793/156250000 : ℝ)^5223 ≤ (372100549779/6250000000000 : ℝ)^4199 := by
    have hnat : (16173793 : ℕ)^5223*6250000000000^4199 ≤ 372100549779^4199*156250000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16173793 156250000 372100549779 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712319923/1250000000 : ℝ)^5223 ≤ (49682575048083/100000000000000 : ℝ)^4199 := by
    have hnat : (712319923 : ℕ)^5223*100000000000000^4199 ≤ 49682575048083^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712319923 1250000000 49682575048083 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202726143/10000000000 : ℝ), (-16173793/156250000 : ℝ), (712319923/1250000000 : ℝ)] ![(2218190807373/5000000000000 : ℝ), (372100549779/6250000000000 : ℝ), (49682575048083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202726143/10000000000 : ℝ)|^5223 ≤ (2218190807373/5000000000000 : ℝ)^4199
        have hw : |(5202726143/10000000000 : ℝ)|=(5202726143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16173793/156250000 : ℝ)|^5223 ≤ (372100549779/6250000000000 : ℝ)^4199
        have hw : |(-16173793/156250000 : ℝ)|=(16173793/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(712319923/1250000000 : ℝ)|^5223 ≤ (49682575048083/100000000000000 : ℝ)^4199
        have hw : |(712319923/1250000000 : ℝ)|=(712319923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_6 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202726287/10000000000 : ℝ)*x 0 + (1424639889/2500000000 : ℝ)*x 1 + (-517561139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202726287/10000000000 : ℝ)^5223 ≤ (11090954418699/25000000000000 : ℝ)^4199 := by
    have hnat : (5202726287 : ℕ)^5223*25000000000000^4199 ≤ 11090954418699^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202726287 10000000000 11090954418699 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424639889/2500000000 : ℝ)^5223 ≤ (49682576913353/100000000000000 : ℝ)^4199 := by
    have hnat : (1424639889 : ℕ)^5223*100000000000000^4199 ≤ 49682576913353^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424639889 2500000000 49682576913353 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517561139/5000000000 : ℝ)^5223 ≤ (2976802702681/50000000000000 : ℝ)^4199 := by
    have hnat : (517561139 : ℕ)^5223*50000000000000^4199 ≤ 2976802702681^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517561139 5000000000 2976802702681 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202726287/10000000000 : ℝ), (1424639889/2500000000 : ℝ), (-517561139/5000000000 : ℝ)] ![(11090954418699/25000000000000 : ℝ), (49682576913353/100000000000000 : ℝ), (2976802702681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202726287/10000000000 : ℝ)|^5223 ≤ (11090954418699/25000000000000 : ℝ)^4199
        have hw : |(5202726287/10000000000 : ℝ)|=(5202726287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424639889/2500000000 : ℝ)|^5223 ≤ (49682576913353/100000000000000 : ℝ)^4199
        have hw : |(1424639889/2500000000 : ℝ)|=(1424639889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517561139/5000000000 : ℝ)|^5223 ≤ (2976802702681/50000000000000 : ℝ)^4199
        have hw : |(-517561139/5000000000 : ℝ)|=(517561139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s0_7 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4053216259/10000000000 : ℝ)*x 0 + (5177582209/10000000000 : ℝ)*x 1 + (777252277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4053216259/10000000000 : ℝ)^5223 ≤ (32520323240543/100000000000000 : ℝ)^4199 := by
    have hnat : (4053216259 : ℕ)^5223*100000000000000^4199 ≤ 32520323240543^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053216259 10000000000 32520323240543 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177582209/10000000000 : ℝ)^5223 ≤ (2204864218431/5000000000000 : ℝ)^4199 := by
    have hnat : (5177582209 : ℕ)^5223*5000000000000^4199 ≤ 2204864218431^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177582209 10000000000 2204864218431 5000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777252277/2500000000 : ℝ)^5223 ≤ (23382392379733/100000000000000 : ℝ)^4199 := by
    have hnat : (777252277 : ℕ)^5223*100000000000000^4199 ≤ 23382392379733^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777252277 2500000000 23382392379733 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4053216259/10000000000 : ℝ), (5177582209/10000000000 : ℝ), (777252277/2500000000 : ℝ)] ![(32520323240543/100000000000000 : ℝ), (2204864218431/5000000000000 : ℝ), (23382392379733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4053216259/10000000000 : ℝ)|^5223 ≤ (32520323240543/100000000000000 : ℝ)^4199
        have hw : |(4053216259/10000000000 : ℝ)|=(4053216259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177582209/10000000000 : ℝ)|^5223 ≤ (2204864218431/5000000000000 : ℝ)^4199
        have hw : |(5177582209/10000000000 : ℝ)|=(5177582209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777252277/2500000000 : ℝ)|^5223 ≤ (23382392379733/100000000000000 : ℝ)^4199
        have hw : |(777252277/2500000000 : ℝ)|=(777252277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5751/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11133/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5215/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5215 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5215*1^1024 ≤ 0^1024*1^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5215/1024 : ℝ) ≤ (940549580623020053/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5215 ≤ (940549580623020053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5215*100000000000000000000^1024 ≤ 940549580623020053^1024*5^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 940549580623020053 100000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (940549580623020053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5215 := by
      have hnat : (1 : ℕ)^1024*1^5215 ≤ 1^5215*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100940549580623020053/100000000000000000000 : ℝ) ≤ (1252299863993449/1250000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (100940549580623020053/100000000000000000000 : ℝ)^1024 ≤ (1252299863993449/1250000000000000 : ℝ)^5215 := by
      have hnat : (100940549580623020053 : ℕ)^1024*1250000000000000^5215 ≤ 1252299863993449^5215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100940549580623020053 100000000000000000000 1252299863993449 1250000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252299863993449/1250000000000000 : ℝ)) (X := (100940549580623020053/100000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50940549580623020053/50000000000000000000 : ℝ) ≤ (627299863993449/625000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (50940549580623020053/50000000000000000000 : ℝ)^1024 ≤ (627299863993449/625000000000000 : ℝ)^5215 := by
      have hnat : (50940549580623020053 : ℕ)^1024*625000000000000^5215 ≤ 627299863993449^5215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50940549580623020053 50000000000000000000 627299863993449 625000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627299863993449/625000000000000 : ℝ)) (X := (50940549580623020053/50000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2299863993449/500000000000000 : ℝ)*(0 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2299863993449/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(940549580623020053/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2299863993449/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2299863993449/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1252299863993449/1250000000000000 : ℝ) by norm_num, show 1+(940549580623020053/100000000000000000000 : ℝ)+(0 : ℝ)=(100940549580623020053/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(940549580623020053/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2299863993449/500000000000000 : ℝ)*(2/5 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2299863993449/500000000000000 : ℝ)*(2/5 : ℝ)=(627299863993449/625000000000000 : ℝ) by norm_num, show 1+2*(940549580623020053/100000000000000000000 : ℝ)=(50940549580623020053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2299863993449/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2299863993449/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2299863993449/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2299863993449/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2299863993449/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2299863993449/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1366557933/10000000000 : ℝ)*X 0 0+(228732371/400000000 : ℝ)*X 0 1+(4949335133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411350423/10000000000 : ℝ)*X 1 0+(-178434727/1000000000 : ℝ)*X 1 1+(9666669/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411349753/10000000000 : ℝ)*X 2 0+(4949335143/10000000000 : ℝ)*X 2 1+(-11152171/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1012007029/2500000000 : ℝ)*X 0 0+(305305557/1000000000 : ℝ)*X 0 1+(2615850293/5000000000 : ℝ)*X 0 2+(1012007029/2500000000 : ℝ)*X 1 0+(305305557/1000000000 : ℝ)*X 1 1+(2615850293/5000000000 : ℝ)*X 1 2+(1012007029/2500000000 : ℝ)*X 2 0+(305305557/1000000000 : ℝ)*X 2 1+(2615850293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1368389863/10000000000 : ℝ)*X 0 0+(993687321/2000000000 : ℝ)*X 0 1+(1139711897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202726143/10000000000 : ℝ)*X 1 0+(-16173793/156250000 : ℝ)*X 1 1+(712319923/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202726287/10000000000 : ℝ)*X 2 0+(1424639889/2500000000 : ℝ)*X 2 1+(-517561139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4053216259/10000000000 : ℝ)*X 0 0+(5177582209/10000000000 : ℝ)*X 0 1+(777252277/2500000000 : ℝ)*X 0 2+(4053216259/10000000000 : ℝ)*X 1 0+(5177582209/10000000000 : ℝ)*X 1 1+(777252277/2500000000 : ℝ)*X 1 2+(4053216259/10000000000 : ℝ)*X 2 0+(5177582209/10000000000 : ℝ)*X 2 1+(777252277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1455085775762510501583/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15353407/12500000000000 : ℝ)*(base1) + (255109763/50000000000000 : ℝ)*(base19) + (34920767/10000000000000 : ℝ)*(base23) + (41204869/50000000000000 : ℝ)*(upper3) + (1597267/12500000000000 : ℝ)*(upper5) + (21992962479439/2500000000000 : ℝ)*(major0) + (21992962479439/2500000000000 : ℝ)*(major1) + (21992962479439/2500000000000 : ℝ)*(major2) + (650217593343341/50000000000000 : ℝ)*(sp0) + (325108757924911/25000000000000 : ℝ)*(sp1) + (2600870385423/200000000000 : ℝ)*(sp2) + (3585945306243/781250000000 : ℝ)*(sp3) + (14939367/3125000000000 : ℝ)*(sp4) + (25680501/10000000000000 : ℝ)*(sp7) + (459001378831371/100000000000000 : ℝ)*(f.failure) + (130043554191917/10000000000000 : ℝ)*(f.sum) + (605995727389/625000000000000000000000000 : ℝ)*base66 + (1688883104889/1250000000000000000000000000 : ℝ)*base68 + (3285122482611/1250000000000000000000000000 : ℝ)*base69 + (7609675637389/1250000000000000000000000000 : ℝ)*base72 + (516027888861/625000000000000000000000000 : ℝ)*base73 + (2865924374889/1250000000000000000000000000 : ℝ)*base76 + (2555813247389/1250000000000000000000000000 : ℝ)*base78 + (5119057892389/1250000000000000000000000000 : ℝ)*base80 + (1142301930111/625000000000000000000000000 : ℝ)*base81 + (27010397/2500000000000000000000 : ℝ)*base89 + (27010397/2500000000000000000000 : ℝ)*base91 + (27010397/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9112897009237803/6250000000000000000000 : ℝ) := by norm_num
    linear_combination (718537169/100000000000000 : ℝ)*(base19) + (431011563/50000000000000 : ℝ)*(base23) + (2109951/6250000000000 : ℝ)*(upper2) + (24852169/20000000000000 : ℝ)*(upper3) + (123413053/100000000000000 : ℝ)*(upper5) + (926528710589651/100000000000000 : ℝ)*(major0) + (926528710589651/100000000000000 : ℝ)*(major1) + (926528710589651/100000000000000 : ℝ)*(major2) + (1141048403/50000000000000 : ℝ)*(sp1) + (1648424009/50000000000000 : ℝ)*(sp2) + (171204040856883/12500000000000 : ℝ)*(sp4) + (1369629326221089/100000000000000 : ℝ)*(sp5) + (1369628167983919/100000000000000 : ℝ)*(sp6) + (241712522861057/50000000000000 : ℝ)*(sp7) + (241712522861057/50000000000000 : ℝ)*(f.failure) + (171204040856883/12500000000000 : ℝ)*(f.sum) + (97796491153701/25000000000000000000000000000 : ℝ)*base66 + (391950013896299/50000000000000000000000000000 : ℝ)*base67 + (234500426403701/50000000000000000000000000000 : ℝ)*base70 + (243827881646299/50000000000000000000000000000 : ℝ)*base71 + (19116059246299/25000000000000000000000000000 : ℝ)*base73 + (83324661603701/50000000000000000000000000000 : ℝ)*base76 + (71620899546299/50000000000000000000000000000 : ℝ)*base77 + (542857072996299/50000000000000000000000000000 : ℝ)*base79 + (150496467553701/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3529001/1250000000000000000000 : ℝ)*base90 + (3529001/1250000000000000000000 : ℝ)*base92 + (3529001/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1700_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5751/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11133/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1700_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1700_s1_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1444528403/10000000000 : ℝ)*x 0 + (343424111/625000000 : ℝ)*x 1 + (5121672869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1444528403/10000000000 : ℝ)^5223 ≤ (9011778593687/100000000000000 : ℝ)^4199 := by
    have hnat : (1444528403 : ℕ)^5223*100000000000000^4199 ≤ 9011778593687^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444528403 10000000000 9011778593687 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343424111/625000000 : ℝ)^5223 ≤ (47482457244639/100000000000000 : ℝ)^4199 := by
    have hnat : (343424111 : ℕ)^5223*100000000000000^4199 ≤ 47482457244639^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343424111 625000000 47482457244639 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121672869/10000000000 : ℝ)^5223 ≤ (10876441039583/25000000000000 : ℝ)^4199 := by
    have hnat : (5121672869 : ℕ)^5223*25000000000000^4199 ≤ 10876441039583^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121672869 10000000000 10876441039583 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1444528403/10000000000 : ℝ), (343424111/625000000 : ℝ), (5121672869/10000000000 : ℝ)] ![(9011778593687/100000000000000 : ℝ), (47482457244639/100000000000000 : ℝ), (10876441039583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1444528403/10000000000 : ℝ)|^5223 ≤ (9011778593687/100000000000000 : ℝ)^4199
        have hw : |(-1444528403/10000000000 : ℝ)|=(1444528403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343424111/625000000 : ℝ)|^5223 ≤ (47482457244639/100000000000000 : ℝ)^4199
        have hw : |(343424111/625000000 : ℝ)|=(343424111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121672869/10000000000 : ℝ)|^5223 ≤ (10876441039583/25000000000000 : ℝ)^4199
        have hw : |(5121672869/10000000000 : ℝ)|=(5121672869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351804069/10000000000 : ℝ)*x 0 + (-819431351/5000000000 : ℝ)*x 1 + (5121672201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351804069/10000000000 : ℝ)^5223 ≤ (45950496198221/100000000000000 : ℝ)^4199 := by
    have hnat : (5351804069 : ℕ)^5223*100000000000000^4199 ≤ 45950496198221^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351804069 10000000000 45950496198221 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (819431351/5000000000 : ℝ)^5223 ≤ (10543746682231/100000000000000 : ℝ)^4199 := by
    have hnat : (819431351 : ℕ)^5223*100000000000000^4199 ≤ 10543746682231^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819431351 5000000000 10543746682231 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121672201/10000000000 : ℝ)^5223 ≤ (10876439275067/25000000000000 : ℝ)^4199 := by
    have hnat : (5121672201 : ℕ)^5223*25000000000000^4199 ≤ 10876439275067^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121672201 10000000000 10876439275067 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351804069/10000000000 : ℝ), (-819431351/5000000000 : ℝ), (5121672201/10000000000 : ℝ)] ![(45950496198221/100000000000000 : ℝ), (10543746682231/100000000000000 : ℝ), (10876439275067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351804069/10000000000 : ℝ)|^5223 ≤ (45950496198221/100000000000000 : ℝ)^4199
        have hw : |(5351804069/10000000000 : ℝ)|=(5351804069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-819431351/5000000000 : ℝ)|^5223 ≤ (10543746682231/100000000000000 : ℝ)^4199
        have hw : |(-819431351/5000000000 : ℝ)|=(819431351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121672201/10000000000 : ℝ)|^5223 ≤ (10876439275067/25000000000000 : ℝ)^4199
        have hw : |(5121672201/10000000000 : ℝ)|=(5121672201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267590143/500000000 : ℝ)*x 0 + (1024334651/2000000000 : ℝ)*x 1 + (-409715731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267590143/500000000 : ℝ)^5223 ≤ (45950483286313/100000000000000 : ℝ)^4199 := by
    have hnat : (267590143 : ℕ)^5223*100000000000000^4199 ≤ 45950483286313^4199*500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267590143 500000000 45950483286313 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024334651/2000000000 : ℝ)^5223 ≤ (21752884118397/50000000000000 : ℝ)^4199 := by
    have hnat : (1024334651 : ℕ)^5223*50000000000000^4199 ≤ 21752884118397^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024334651 2000000000 21752884118397 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409715731/2500000000 : ℝ)^5223 ≤ (1054374845879/10000000000000 : ℝ)^4199 := by
    have hnat : (409715731 : ℕ)^5223*10000000000000^4199 ≤ 1054374845879^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409715731 2500000000 1054374845879 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267590143/500000000 : ℝ), (1024334651/2000000000 : ℝ), (-409715731/2500000000 : ℝ)] ![(45950483286313/100000000000000 : ℝ), (21752884118397/50000000000000 : ℝ), (1054374845879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267590143/500000000 : ℝ)|^5223 ≤ (45950483286313/100000000000000 : ℝ)^4199
        have hw : |(267590143/500000000 : ℝ)|=(267590143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024334651/2000000000 : ℝ)|^5223 ≤ (21752884118397/50000000000000 : ℝ)^4199
        have hw : |(1024334651/2000000000 : ℝ)|=(1024334651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409715731/2500000000 : ℝ)|^5223 ≤ (1054374845879/10000000000000 : ℝ)^4199
        have hw : |(-409715731/2500000000 : ℝ)|=(409715731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4114287123/10000000000 : ℝ)*x 0 + (3607774553/10000000000 : ℝ)*x 1 + (4664872031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4114287123/10000000000 : ℝ)^5223 ≤ (16565462074169/50000000000000 : ℝ)^4199 := by
    have hnat : (4114287123 : ℕ)^5223*50000000000000^4199 ≤ 16565462074169^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114287123 10000000000 16565462074169 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3607774553/10000000000 : ℝ)^5223 ≤ (28136134373339/100000000000000 : ℝ)^4199 := by
    have hnat : (3607774553 : ℕ)^5223*100000000000000^4199 ≤ 28136134373339^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3607774553 10000000000 28136134373339 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4664872031/10000000000 : ℝ)^5223 ≤ (9683235364371/25000000000000 : ℝ)^4199 := by
    have hnat : (4664872031 : ℕ)^5223*25000000000000^4199 ≤ 9683235364371^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664872031 10000000000 9683235364371 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4114287123/10000000000 : ℝ), (3607774553/10000000000 : ℝ), (4664872031/10000000000 : ℝ)] ![(16565462074169/50000000000000 : ℝ), (28136134373339/100000000000000 : ℝ), (9683235364371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4114287123/10000000000 : ℝ)|^5223 ≤ (16565462074169/50000000000000 : ℝ)^4199
        have hw : |(4114287123/10000000000 : ℝ)|=(4114287123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3607774553/10000000000 : ℝ)|^5223 ≤ (28136134373339/100000000000000 : ℝ)^4199
        have hw : |(3607774553/10000000000 : ℝ)|=(3607774553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4664872031/10000000000 : ℝ)|^5223 ≤ (9683235364371/25000000000000 : ℝ)^4199
        have hw : |(4664872031/10000000000 : ℝ)|=(4664872031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-361183597/2500000000 : ℝ)*x 0 + (2563085293/5000000000 : ℝ)*x 1 + (34313843/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361183597/2500000000 : ℝ)^5223 ≤ (9013377053513/100000000000000 : ℝ)^4199 := by
    have hnat : (361183597 : ℕ)^5223*100000000000000^4199 ≤ 9013377053513^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361183597 2500000000 9013377053513 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563085293/5000000000 : ℝ)^5223 ≤ (43553291960701/100000000000000 : ℝ)^4199 := by
    have hnat : (2563085293 : ℕ)^5223*100000000000000^4199 ≤ 43553291960701^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563085293 5000000000 43553291960701 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34313843/62500000 : ℝ)^5223 ≤ (47433330968061/100000000000000 : ℝ)^4199 := by
    have hnat : (34313843 : ℕ)^5223*100000000000000^4199 ≤ 47433330968061^4199*62500000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34313843 62500000 47433330968061 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361183597/2500000000 : ℝ), (2563085293/5000000000 : ℝ), (34313843/62500000 : ℝ)] ![(9013377053513/100000000000000 : ℝ), (43553291960701/100000000000000 : ℝ), (47433330968061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361183597/2500000000 : ℝ)|^5223 ≤ (9013377053513/100000000000000 : ℝ)^4199
        have hw : |(-361183597/2500000000 : ℝ)|=(361183597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563085293/5000000000 : ℝ)|^5223 ≤ (43553291960701/100000000000000 : ℝ)^4199
        have hw : |(2563085293/5000000000 : ℝ)|=(2563085293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34313843/62500000 : ℝ)|^5223 ≤ (47433330968061/100000000000000 : ℝ)^4199
        have hw : |(34313843/62500000 : ℝ)|=(34313843/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625961351/5000000000 : ℝ)*x 0 + (-1270319959/10000000000 : ℝ)*x 1 + (549021497/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625961351/5000000000 : ℝ)^5223 ≤ (22443109821/50000000000 : ℝ)^4199 := by
    have hnat : (2625961351 : ℕ)^5223*50000000000^4199 ≤ 22443109821^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625961351 5000000000 22443109821 50000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270319959/10000000000 : ℝ)^5223 ≤ (7680448412499/100000000000000 : ℝ)^4199 := by
    have hnat : (1270319959 : ℕ)^5223*100000000000000^4199 ≤ 7680448412499^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270319959 10000000000 7680448412499 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549021497/1000000000 : ℝ)^5223 ≤ (47433331935249/100000000000000 : ℝ)^4199 := by
    have hnat : (549021497 : ℕ)^5223*100000000000000^4199 ≤ 47433331935249^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549021497 1000000000 47433331935249 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625961351/5000000000 : ℝ), (-1270319959/10000000000 : ℝ), (549021497/1000000000 : ℝ)] ![(22443109821/50000000000 : ℝ), (7680448412499/100000000000000 : ℝ), (47433331935249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625961351/5000000000 : ℝ)|^5223 ≤ (22443109821/50000000000 : ℝ)^4199
        have hw : |(2625961351/5000000000 : ℝ)|=(2625961351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1270319959/10000000000 : ℝ)|^5223 ≤ (7680448412499/100000000000000 : ℝ)^4199
        have hw : |(-1270319959/10000000000 : ℝ)|=(1270319959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549021497/1000000000 : ℝ)|^5223 ≤ (47433331935249/100000000000000 : ℝ)^4199
        have hw : |(549021497/1000000000 : ℝ)|=(549021497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_6 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251923343/10000000000 : ℝ)*x 0 + (2745107529/5000000000 : ℝ)*x 1 + (-1270318927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251923343/10000000000 : ℝ)^5223 ≤ (44886226456389/100000000000000 : ℝ)^4199 := by
    have hnat : (5251923343 : ℕ)^5223*100000000000000^4199 ≤ 44886226456389^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251923343 10000000000 44886226456389 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745107529/5000000000 : ℝ)^5223 ≤ (2964583305059/6250000000000 : ℝ)^4199 := by
    have hnat : (2745107529 : ℕ)^5223*6250000000000^4199 ≤ 2964583305059^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745107529 5000000000 2964583305059 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270318927/10000000000 : ℝ)^5223 ≤ (120006885177/1562500000000 : ℝ)^4199 := by
    have hnat : (1270318927 : ℕ)^5223*1562500000000^4199 ≤ 120006885177^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270318927 10000000000 120006885177 1562500000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251923343/10000000000 : ℝ), (2745107529/5000000000 : ℝ), (-1270318927/10000000000 : ℝ)] ![(44886226456389/100000000000000 : ℝ), (2964583305059/6250000000000 : ℝ), (120006885177/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251923343/10000000000 : ℝ)|^5223 ≤ (44886226456389/100000000000000 : ℝ)^4199
        have hw : |(5251923343/10000000000 : ℝ)|=(5251923343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745107529/5000000000 : ℝ)|^5223 ≤ (2964583305059/6250000000000 : ℝ)^4199
        have hw : |(2745107529/5000000000 : ℝ)|=(2745107529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1270318927/10000000000 : ℝ)|^5223 ≤ (120006885177/1562500000000 : ℝ)^4199
        have hw : |(-1270318927/10000000000 : ℝ)|=(1270318927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s1_7 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4114875791/10000000000 : ℝ)*x 0 + (930425951/2000000000 : ℝ)*x 1 + (905180717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4114875791/10000000000 : ℝ)^5223 ≤ (33136820604983/100000000000000 : ℝ)^4199 := by
    have hnat : (4114875791 : ℕ)^5223*100000000000000^4199 ≤ 33136820604983^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114875791 10000000000 33136820604983 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930425951/2000000000 : ℝ)^5223 ≤ (3860138349733/10000000000000 : ℝ)^4199 := by
    have hnat : (930425951 : ℕ)^5223*10000000000000^4199 ≤ 3860138349733^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930425951 2000000000 3860138349733 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905180717/2500000000 : ℝ)^5223 ≤ (14130897943819/50000000000000 : ℝ)^4199 := by
    have hnat : (905180717 : ℕ)^5223*50000000000000^4199 ≤ 14130897943819^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905180717 2500000000 14130897943819 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4114875791/10000000000 : ℝ), (930425951/2000000000 : ℝ), (905180717/2500000000 : ℝ)] ![(33136820604983/100000000000000 : ℝ), (3860138349733/10000000000000 : ℝ), (14130897943819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4114875791/10000000000 : ℝ)|^5223 ≤ (33136820604983/100000000000000 : ℝ)^4199
        have hw : |(4114875791/10000000000 : ℝ)|=(4114875791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(930425951/2000000000 : ℝ)|^5223 ≤ (3860138349733/10000000000000 : ℝ)^4199
        have hw : |(930425951/2000000000 : ℝ)|=(930425951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905180717/2500000000 : ℝ)|^5223 ≤ (14130897943819/50000000000000 : ℝ)^4199
        have hw : |(905180717/2500000000 : ℝ)|=(905180717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17547/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11133/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11133/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5751/100000 : ℝ) ^ (5215/1024 : ℝ) ≤ (48267406816241/100000000000000000000 : ℝ) := by
    have hpowers : (5751/100000 : ℝ)^5215 ≤ (48267406816241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5751 : ℕ)^5215*100000000000000000000^1024 ≤ 48267406816241^1024*100000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5751 100000 48267406816241 100000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5751/100000 : ℝ)) (X := (48267406816241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11133/50000 : ℝ) ^ (5215/1024 : ℝ) ≤ (5951131701494337/12500000000000000000 : ℝ) := by
    have hpowers : (11133/50000 : ℝ)^5215 ≤ (5951131701494337/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11133 : ℕ)^5215*12500000000000000000^1024 ≤ 5951131701494337^1024*50000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11133 50000 5951131701494337 12500000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11133/50000 : ℝ)) (X := (5951131701494337/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000048267406816241/50000000000000000000 : ℝ) ≤ (10000001895524657/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (50000048267406816241/50000000000000000000 : ℝ)^1024 ≤ (10000001895524657/10000000000000000 : ℝ)^5215 := by
      have hnat : (50000048267406816241 : ℕ)^1024*10000000000000000^5215 ≤ 10000001895524657^5215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000048267406816241 50000000000000000000 10000001895524657 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001895524657/10000000000000000 : ℝ)) (X := (50000048267406816241/50000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047657321018770937/100000000000000000000 : ℝ) ≤ (2500233901026437/2500000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (100047657321018770937/100000000000000000000 : ℝ)^1024 ≤ (2500233901026437/2500000000000000 : ℝ)^5215 := by
      have hnat : (100047657321018770937 : ℕ)^1024*2500000000000000^5215 ≤ 2500233901026437^5215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047657321018770937 100000000000000000000 2500233901026437 2500000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500233901026437/2500000000000000 : ℝ)) (X := (100047657321018770937/100000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6255951131701494337/6250000000000000000 : ℝ) ≤ (10001869312686839/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (6255951131701494337/6250000000000000000 : ℝ)^1024 ≤ (10001869312686839/10000000000000000 : ℝ)^5215 := by
      have hnat : (6255951131701494337 : ℕ)^1024*10000000000000000^5215 ≤ 10001869312686839^5215*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255951131701494337 6250000000000000000 10001869312686839 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001869312686839/10000000000000000 : ℝ)) (X := (6255951131701494337/6250000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48267406816241/100000000000000000000 : ℝ) ≤ ((18348810198721111297/18350000000000000000 : ℝ)+2*(103745397899/183500000000000 : ℝ)*(5751/100000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (18348810198721111297/18350000000000000000 : ℝ)+2*(103745397899/183500000000000 : ℝ)*(5751/100000 : ℝ)=(10000001895524657/10000000000000000 : ℝ) by norm_num, show 1+2*(48267406816241/100000000000000000000 : ℝ)=(50000048267406816241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5951131701494337/12500000000000000000 : ℝ)+(48267406816241/100000000000000000000 : ℝ) ≤ ((18348810198721111297/18350000000000000000 : ℝ)+(103745397899/183500000000000 : ℝ)*((11133/50000 : ℝ)+(5751/100000 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (18348810198721111297/18350000000000000000 : ℝ)+(103745397899/183500000000000 : ℝ)*((11133/50000 : ℝ)+(5751/100000 : ℝ))=(2500233901026437/2500000000000000 : ℝ) by norm_num, show 1+(5951131701494337/12500000000000000000 : ℝ)+(48267406816241/100000000000000000000 : ℝ)=(100047657321018770937/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5951131701494337/12500000000000000000 : ℝ) ≤ ((18348810198721111297/18350000000000000000 : ℝ)+2*(103745397899/183500000000000 : ℝ)*(11133/50000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (18348810198721111297/18350000000000000000 : ℝ)+2*(103745397899/183500000000000 : ℝ)*(11133/50000 : ℝ)=(10001869312686839/10000000000000000 : ℝ) by norm_num, show 1+2*(5951131701494337/12500000000000000000 : ℝ)=(6255951131701494337/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18348810198721111297/18350000000000000000 : ℝ)*(X 1 0+X 2 0)+(103745397899/183500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (5751/100000 : ℝ)) (hi := (11133/50000 : ℝ)) (c := (18348810198721111297/18350000000000000000 : ℝ)) (alpha := (103745397899/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18348810198721111297/18350000000000000000 : ℝ)*(X 0 1+X 2 1)+(103745397899/183500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (5751/100000 : ℝ)) (hi := (11133/50000 : ℝ)) (c := (18348810198721111297/18350000000000000000 : ℝ)) (alpha := (103745397899/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18348810198721111297/18350000000000000000 : ℝ)*(X 0 2+X 1 2)+(103745397899/183500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (5751/100000 : ℝ)) (hi := (11133/50000 : ℝ)) (c := (18348810198721111297/18350000000000000000 : ℝ)) (alpha := (103745397899/183500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1444528403/10000000000 : ℝ)*X 0 0+(343424111/625000000 : ℝ)*X 0 1+(5121672869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351804069/10000000000 : ℝ)*X 1 0+(-819431351/5000000000 : ℝ)*X 1 1+(5121672201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267590143/500000000 : ℝ)*X 2 0+(1024334651/2000000000 : ℝ)*X 2 1+(-409715731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4114287123/10000000000 : ℝ)*X 0 0+(3607774553/10000000000 : ℝ)*X 0 1+(4664872031/10000000000 : ℝ)*X 0 2+(4114287123/10000000000 : ℝ)*X 1 0+(3607774553/10000000000 : ℝ)*X 1 1+(4664872031/10000000000 : ℝ)*X 1 2+(4114287123/10000000000 : ℝ)*X 2 0+(3607774553/10000000000 : ℝ)*X 2 1+(4664872031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-361183597/2500000000 : ℝ)*X 0 0+(2563085293/5000000000 : ℝ)*X 0 1+(34313843/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625961351/5000000000 : ℝ)*X 1 0+(-1270319959/10000000000 : ℝ)*X 1 1+(549021497/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251923343/10000000000 : ℝ)*X 2 0+(2745107529/5000000000 : ℝ)*X 2 1+(-1270318927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4114875791/10000000000 : ℝ)*X 0 0+(930425951/2000000000 : ℝ)*X 0 1+(905180717/2500000000 : ℝ)*X 0 2+(4114875791/10000000000 : ℝ)*X 1 0+(930425951/2000000000 : ℝ)*X 1 1+(905180717/2500000000 : ℝ)*X 1 2+(4114875791/10000000000 : ℝ)*X 2 0+(930425951/2000000000 : ℝ)*X 2 1+(905180717/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6244923494479113617661317883/458750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60528431/3125000000000 : ℝ)*(base19) + (1230163931/100000000000000 : ℝ)*(base23) + (423459/781250000000 : ℝ)*(lower2) + (371466301/100000000000000 : ℝ)*(upper3) + (558459/800000000000 : ℝ)*(upper5) + (906544523736771/50000000000000 : ℝ)*(major0) + (906544523736771/50000000000000 : ℝ)*(major1) + (906544523736771/50000000000000 : ℝ)*(major2) + (2680170722388687/100000000000000 : ℝ)*(sp0) + (1340089743359681/50000000000000 : ℝ)*(sp1) + (1340090096732611/50000000000000 : ℝ)*(sp2) + (236497680306681/25000000000000 : ℝ)*(sp3) + (5350620233/50000000000000 : ℝ)*(sp4) + (5496327457/100000000000000 : ℝ)*(sp7) + (47299810877709/5000000000000 : ℝ)*(f.failure) + (1340090711814577/50000000000000 : ℝ)*(f.sum) + (5144422517999/1146875000000000000000000000 : ℝ)*base66 + (5052311728277198013/917500000000000000000000000000000 : ℝ)*base68 + (3203295638617198013/917500000000000000000000000000000 : ℝ)*base70 + (6301640211712198013/917500000000000000000000000000000 : ℝ)*base72 + (16667804383267/9175000000000000000000000000 : ℝ)*base74 + (7856937001599698013/917500000000000000000000000000000 : ℝ)*base76 + (2078801450997198013/917500000000000000000000000000000 : ℝ)*base78 + (5691798605462198013/917500000000000000000000000000000 : ℝ)*base80 + (35645182994171/4587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (162837/125000000000000000000 : ℝ)*base90 + (162837/125000000000000000000 : ℝ)*base92 + (162837/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (761418512659219743673409361/229375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286361171/100000000000000 : ℝ)*(base19) + (474565899/25000000000000 : ℝ)*(base23) + (9665269/10000000000000 : ℝ)*(upper3) + (496228863/100000000000000 : ℝ)*(lower4) + (464557821620829/25000000000000 : ℝ)*(major0) + (464557821620829/25000000000000 : ℝ)*(major1) + (464557821620829/25000000000000 : ℝ)*(major2) + (12128057/781250000000 : ℝ)*(sp1) + (18998723703/100000000000000 : ℝ)*(sp2) + (172331537/50000000000000 : ℝ)*(sp3) + (68672821452931/2500000000000 : ℝ)*(sp4) + (686727754841193/25000000000000 : ℝ)*(sp5) + (137344598056497/5000000000000 : ℝ)*(sp6) + (969549259535121/100000000000000 : ℝ)*(sp7) + (193909920839639/20000000000000 : ℝ)*(f.failure) + (68672821452931/2500000000000 : ℝ)*(f.sum) + (8156192744809/9175000000000000000000000000 : ℝ)*base65 + (971281490454244787/458750000000000000000000000000000 : ℝ)*base68 + (2594191091747994787/458750000000000000000000000000000 : ℝ)*base70 + (1016617469685755213/458750000000000000000000000000000 : ℝ)*base71 + (4921415928891/9175000000000000000000000000 : ℝ)*base74 + (3328240150862005213/458750000000000000000000000000000 : ℝ)*base75 + (1792573537255755213/458750000000000000000000000000000 : ℝ)*base77 + (4054417819277005213/458750000000000000000000000000000 : ℝ)*base79 + (2961723670833/4587500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (634673/500000000000000000000 : ℝ)*base89 + (634673/500000000000000000000 : ℝ)*base91 + (634673/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1700_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17547/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1700_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1700_s2_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1448844943/10000000000 : ℝ)*x 0 + (5477275621/10000000000 : ℝ)*x 1 + (128407563/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1448844943/10000000000 : ℝ)^5223 ≤ (9045286897267/100000000000000 : ℝ)^4199 := by
    have hnat : (1448844943 : ℕ)^5223*100000000000000^4199 ≤ 9045286897267^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448844943 10000000000 9045286897267 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477275621/10000000000 : ℝ)^5223 ≤ (47294318759811/100000000000000 : ℝ)^4199 := by
    have hnat : (5477275621 : ℕ)^5223*100000000000000^4199 ≤ 47294318759811^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477275621 10000000000 47294318759811 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128407563/250000000 : ℝ)^5223 ≤ (1364387322497/3125000000000 : ℝ)^4199 := by
    have hnat : (128407563 : ℕ)^5223*3125000000000^4199 ≤ 1364387322497^4199*250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128407563 250000000 1364387322497 3125000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1448844943/10000000000 : ℝ), (5477275621/10000000000 : ℝ), (128407563/250000000 : ℝ)] ![(9045286897267/100000000000000 : ℝ), (47294318759811/100000000000000 : ℝ), (1364387322497/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1448844943/10000000000 : ℝ)|^5223 ≤ (9045286897267/100000000000000 : ℝ)^4199
        have hw : |(-1448844943/10000000000 : ℝ)|=(1448844943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477275621/10000000000 : ℝ)|^5223 ≤ (47294318759811/100000000000000 : ℝ)^4199
        have hw : |(5477275621/10000000000 : ℝ)|=(5477275621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128407563/250000000 : ℝ)|^5223 ≤ (1364387322497/3125000000000 : ℝ)^4199
        have hw : |(128407563/250000000 : ℝ)|=(128407563/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347083069/10000000000 : ℝ)*x 0 + (-1625825763/10000000000 : ℝ)*x 1 + (642037859/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347083069/10000000000 : ℝ)^5223 ≤ (22950041083539/50000000000000 : ℝ)^4199 := by
    have hnat : (5347083069 : ℕ)^5223*50000000000000^4199 ≤ 22950041083539^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347083069 10000000000 22950041083539 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1625825763/10000000000 : ℝ)^5223 ≤ (5219759884957/50000000000000 : ℝ)^4199 := by
    have hnat : (1625825763 : ℕ)^5223*50000000000000^4199 ≤ 5219759884957^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625825763 10000000000 5219759884957 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642037859/1250000000 : ℝ)^5223 ≤ (43660398041711/100000000000000 : ℝ)^4199 := by
    have hnat : (642037859 : ℕ)^5223*100000000000000^4199 ≤ 43660398041711^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642037859 1250000000 43660398041711 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347083069/10000000000 : ℝ), (-1625825763/10000000000 : ℝ), (642037859/1250000000 : ℝ)] ![(22950041083539/50000000000000 : ℝ), (5219759884957/50000000000000 : ℝ), (43660398041711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347083069/10000000000 : ℝ)|^5223 ≤ (22950041083539/50000000000000 : ℝ)^4199
        have hw : |(5347083069/10000000000 : ℝ)|=(5347083069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1625825763/10000000000 : ℝ)|^5223 ≤ (5219759884957/50000000000000 : ℝ)^4199
        have hw : |(-1625825763/10000000000 : ℝ)|=(1625825763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642037859/1250000000 : ℝ)|^5223 ≤ (43660398041711/100000000000000 : ℝ)^4199
        have hw : |(642037859/1250000000 : ℝ)|=(642037859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347082767/10000000000 : ℝ)*x 0 + (2568151447/5000000000 : ℝ)*x 1 + (-1625826139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347082767/10000000000 : ℝ)^5223 ≤ (9180015788493/20000000000000 : ℝ)^4199 := by
    have hnat : (5347082767 : ℕ)^5223*20000000000000^4199 ≤ 9180015788493^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347082767 10000000000 9180015788493 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568151447/5000000000 : ℝ)^5223 ≤ (10915099568581/25000000000000 : ℝ)^4199 := by
    have hnat : (2568151447 : ℕ)^5223*25000000000000^4199 ≤ 10915099568581^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568151447 5000000000 10915099568581 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625826139/10000000000 : ℝ)^5223 ≤ (2087904554601/20000000000000 : ℝ)^4199 := by
    have hnat : (1625826139 : ℕ)^5223*20000000000000^4199 ≤ 2087904554601^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625826139 10000000000 2087904554601 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347082767/10000000000 : ℝ), (2568151447/5000000000 : ℝ), (-1625826139/10000000000 : ℝ)] ![(9180015788493/20000000000000 : ℝ), (10915099568581/25000000000000 : ℝ), (2087904554601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347082767/10000000000 : ℝ)|^5223 ≤ (9180015788493/20000000000000 : ℝ)^4199
        have hw : |(5347082767/10000000000 : ℝ)|=(5347082767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568151447/5000000000 : ℝ)|^5223 ≤ (10915099568581/25000000000000 : ℝ)^4199
        have hw : |(2568151447/5000000000 : ℝ)|=(2568151447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625826139/10000000000 : ℝ)|^5223 ≤ (2087904554601/20000000000000 : ℝ)^4199
        have hw : |(-1625826139/10000000000 : ℝ)|=(1625826139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058809909/5000000000 : ℝ)*x 0 + (365300119/1000000000 : ℝ)*x 1 + (2309520177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058809909/5000000000 : ℝ)^5223 ≤ (1326572366483/4000000000000 : ℝ)^4199 := by
    have hnat : (2058809909 : ℕ)^5223*4000000000000^4199 ≤ 1326572366483^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058809909 5000000000 1326572366483 4000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365300119/1000000000 : ℝ)^5223 ≤ (5715105798677/20000000000000 : ℝ)^4199 := by
    have hnat : (365300119 : ℕ)^5223*20000000000000^4199 ≤ 5715105798677^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365300119 1000000000 5715105798677 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2309520177/5000000000 : ℝ)^5223 ≤ (38260161822969/100000000000000 : ℝ)^4199 := by
    have hnat : (2309520177 : ℕ)^5223*100000000000000^4199 ≤ 38260161822969^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309520177 5000000000 38260161822969 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058809909/5000000000 : ℝ), (365300119/1000000000 : ℝ), (2309520177/5000000000 : ℝ)] ![(1326572366483/4000000000000 : ℝ), (5715105798677/20000000000000 : ℝ), (38260161822969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058809909/5000000000 : ℝ)|^5223 ≤ (1326572366483/4000000000000 : ℝ)^4199
        have hw : |(2058809909/5000000000 : ℝ)|=(2058809909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(365300119/1000000000 : ℝ)|^5223 ≤ (5715105798677/20000000000000 : ℝ)^4199
        have hw : |(365300119/1000000000 : ℝ)|=(365300119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2309520177/5000000000 : ℝ)|^5223 ≤ (38260161822969/100000000000000 : ℝ)^4199
        have hw : |(2309520177/5000000000 : ℝ)|=(2309520177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1449002617/10000000000 : ℝ)*x 0 + (5140061171/10000000000 : ℝ)*x 1 + (5473460767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1449002617/10000000000 : ℝ)^5223 ≤ (9046511345521/100000000000000 : ℝ)^4199 := by
    have hnat : (1449002617 : ℕ)^5223*100000000000000^4199 ≤ 9046511345521^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449002617 10000000000 9046511345521 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140061171/10000000000 : ℝ)^5223 ≤ (5462517408737/12500000000000 : ℝ)^4199 := by
    have hnat : (5140061171 : ℕ)^5223*12500000000000^4199 ≤ 5462517408737^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140061171 10000000000 5462517408737 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473460767/10000000000 : ℝ)^5223 ≤ (4725334936387/10000000000000 : ℝ)^4199 := by
    have hnat : (5473460767 : ℕ)^5223*10000000000000^4199 ≤ 4725334936387^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473460767 10000000000 4725334936387 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1449002617/10000000000 : ℝ), (5140061171/10000000000 : ℝ), (5473460767/10000000000 : ℝ)] ![(9046511345521/100000000000000 : ℝ), (5462517408737/12500000000000 : ℝ), (4725334936387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1449002617/10000000000 : ℝ)|^5223 ≤ (9046511345521/100000000000000 : ℝ)^4199
        have hw : |(-1449002617/10000000000 : ℝ)|=(1449002617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140061171/10000000000 : ℝ)|^5223 ≤ (5462517408737/12500000000000 : ℝ)^4199
        have hw : |(5140061171/10000000000 : ℝ)|=(5140061171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473460767/10000000000 : ℝ)|^5223 ≤ (4725334936387/10000000000000 : ℝ)^4199
        have hw : |(5473460767/10000000000 : ℝ)|=(5473460767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255849859/10000000000 : ℝ)*x 0 + (-161083513/1250000000 : ℝ)*x 1 + (171045649/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255849859/10000000000 : ℝ)^5223 ≤ (8985594509607/20000000000000 : ℝ)^4199 := by
    have hnat : (5255849859 : ℕ)^5223*20000000000000^4199 ≤ 8985594509607^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255849859 10000000000 8985594509607 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161083513/1250000000 : ℝ)^5223 ≤ (977334757653/12500000000000 : ℝ)^4199 := by
    have hnat : (161083513 : ℕ)^5223*12500000000000^4199 ≤ 977334757653^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161083513 1250000000 977334757653 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171045649/312500000 : ℝ)^5223 ≤ (47253349374609/100000000000000 : ℝ)^4199 := by
    have hnat : (171045649 : ℕ)^5223*100000000000000^4199 ≤ 47253349374609^4199*312500000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171045649 312500000 47253349374609 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255849859/10000000000 : ℝ), (-161083513/1250000000 : ℝ), (171045649/312500000 : ℝ)] ![(8985594509607/20000000000000 : ℝ), (977334757653/12500000000000 : ℝ), (47253349374609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255849859/10000000000 : ℝ)|^5223 ≤ (8985594509607/20000000000000 : ℝ)^4199
        have hw : |(5255849859/10000000000 : ℝ)|=(5255849859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161083513/1250000000 : ℝ)|^5223 ≤ (977334757653/12500000000000 : ℝ)^4199
        have hw : |(-161083513/1250000000 : ℝ)|=(161083513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171045649/312500000 : ℝ)|^5223 ≤ (47253349374609/100000000000000 : ℝ)^4199
        have hw : |(171045649/312500000 : ℝ)|=(171045649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_6 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255849853/10000000000 : ℝ)*x 0 + (1368365193/2500000000 : ℝ)*x 1 + (-644334053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255849853/10000000000 : ℝ)^5223 ≤ (22463986242119/50000000000000 : ℝ)^4199 := by
    have hnat : (5255849853 : ℕ)^5223*50000000000000^4199 ≤ 22463986242119^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255849853 10000000000 22463986242119 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368365193/2500000000 : ℝ)^5223 ≤ (47253349417563/100000000000000 : ℝ)^4199 := by
    have hnat : (1368365193 : ℕ)^5223*100000000000000^4199 ≤ 47253349417563^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368365193 2500000000 47253349417563 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644334053/5000000000 : ℝ)^5223 ≤ (3909339038159/50000000000000 : ℝ)^4199 := by
    have hnat : (644334053 : ℕ)^5223*50000000000000^4199 ≤ 3909339038159^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644334053 5000000000 3909339038159 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255849853/10000000000 : ℝ), (1368365193/2500000000 : ℝ), (-644334053/5000000000 : ℝ)] ![(22463986242119/50000000000000 : ℝ), (47253349417563/100000000000000 : ℝ), (3909339038159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255849853/10000000000 : ℝ)|^5223 ≤ (22463986242119/50000000000000 : ℝ)^4199
        have hw : |(5255849853/10000000000 : ℝ)|=(5255849853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368365193/2500000000 : ℝ)|^5223 ≤ (47253349417563/100000000000000 : ℝ)^4199
        have hw : |(1368365193/2500000000 : ℝ)|=(1368365193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-644334053/5000000000 : ℝ)|^5223 ≤ (3909339038159/50000000000000 : ℝ)^4199
        have hw : |(-644334053/5000000000 : ℝ)|=(644334053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s2_7 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4118066731/10000000000 : ℝ)*x 0 + (4608391971/10000000000 : ℝ)*x 1 + (1831904711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118066731/10000000000 : ℝ)^5223 ≤ (33168786579611/100000000000000 : ℝ)^4199 := by
    have hnat : (4118066731 : ℕ)^5223*100000000000000^4199 ≤ 33168786579611^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118066731 10000000000 33168786579611 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4608391971/10000000000 : ℝ)^5223 ≤ (19075240500849/50000000000000 : ℝ)^4199 := by
    have hnat : (4608391971 : ℕ)^5223*50000000000000^4199 ≤ 19075240500849^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608391971 10000000000 19075240500849 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831904711/5000000000 : ℝ)^5223 ≤ (28680732401601/100000000000000 : ℝ)^4199 := by
    have hnat : (1831904711 : ℕ)^5223*100000000000000^4199 ≤ 28680732401601^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831904711 5000000000 28680732401601 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118066731/10000000000 : ℝ), (4608391971/10000000000 : ℝ), (1831904711/5000000000 : ℝ)] ![(33168786579611/100000000000000 : ℝ), (19075240500849/50000000000000 : ℝ), (28680732401601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118066731/10000000000 : ℝ)|^5223 ≤ (33168786579611/100000000000000 : ℝ)^4199
        have hw : |(4118066731/10000000000 : ℝ)|=(4118066731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4608391971/10000000000 : ℝ)|^5223 ≤ (19075240500849/50000000000000 : ℝ)^4199
        have hw : |(4608391971/10000000000 : ℝ)|=(4608391971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1831904711/5000000000 : ℝ)|^5223 ≤ (28680732401601/100000000000000 : ℝ)^4199
        have hw : |(1831904711/5000000000 : ℝ)|=(1831904711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1239/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (859/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9593/100000 : ℝ) ^ (5215/1024 : ℝ) ≤ (5106398066553/781250000000000000 : ℝ) := by
    have hpowers : (9593/100000 : ℝ)^5215 ≤ (5106398066553/781250000000000000 : ℝ)^1024 := by
      have hnat : (9593 : ℕ)^5215*781250000000000000^1024 ≤ 5106398066553^1024*100000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9593 100000 5106398066553 781250000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9593/100000 : ℝ)) (X := (5106398066553/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17547/100000 : ℝ) ^ (5215/1024 : ℝ) ≤ (14154563568128367/100000000000000000000 : ℝ) := by
    have hpowers : (17547/100000 : ℝ)^5215 ≤ (14154563568128367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17547 : ℕ)^5215*100000000000000000000^1024 ≤ 14154563568128367^1024*100000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17547 100000 14154563568128367 100000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17547/100000 : ℝ)) (X := (14154563568128367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (390630106398066553/390625000000000000 : ℝ) ≤ (10000025668352511/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (390630106398066553/390625000000000000 : ℝ)^1024 ≤ (10000025668352511/10000000000000000 : ℝ)^5215 := by
      have hnat : (390630106398066553 : ℕ)^1024*10000000000000000^5215 ≤ 10000025668352511^5215*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390630106398066553 390625000000000000 10000025668352511 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000025668352511/10000000000000000 : ℝ)) (X := (390630106398066553/390625000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014808182520647151/100000000000000000000 : ℝ) ≤ (1250036343903909/1250000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (100014808182520647151/100000000000000000000 : ℝ)^1024 ≤ (1250036343903909/1250000000000000 : ℝ)^5215 := by
      have hnat : (100014808182520647151 : ℕ)^1024*1250000000000000^5215 ≤ 1250036343903909^5215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014808182520647151 100000000000000000000 1250036343903909 1250000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036343903909/1250000000000000 : ℝ)) (X := (100014808182520647151/100000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014154563568128367/50000000000000000000 : ℝ) ≤ (10000555834110033/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (50014154563568128367/50000000000000000000 : ℝ)^1024 ≤ (10000555834110033/10000000000000000 : ℝ)^5215 := by
      have hnat : (50014154563568128367 : ℕ)^1024*10000000000000000^5215 ≤ 10000555834110033^5215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014154563568128367 50000000000000000000 10000555834110033 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000555834110033/10000000000000000 : ℝ)) (X := (50014154563568128367/50000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5106398066553/781250000000000000 : ℝ) ≤ ((19883779571490990987/19885000000000000000 : ℝ)+2*(265082878761/795400000000000 : ℝ)*(9593/100000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (19883779571490990987/19885000000000000000 : ℝ)+2*(265082878761/795400000000000 : ℝ)*(9593/100000 : ℝ)=(10000025668352511/10000000000000000 : ℝ) by norm_num, show 1+2*(5106398066553/781250000000000000 : ℝ)=(390630106398066553/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14154563568128367/100000000000000000000 : ℝ)+(5106398066553/781250000000000000 : ℝ) ≤ ((19883779571490990987/19885000000000000000 : ℝ)+(265082878761/795400000000000 : ℝ)*((17547/100000 : ℝ)+(9593/100000 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (19883779571490990987/19885000000000000000 : ℝ)+(265082878761/795400000000000 : ℝ)*((17547/100000 : ℝ)+(9593/100000 : ℝ))=(1250036343903909/1250000000000000 : ℝ) by norm_num, show 1+(14154563568128367/100000000000000000000 : ℝ)+(5106398066553/781250000000000000 : ℝ)=(100014808182520647151/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14154563568128367/100000000000000000000 : ℝ) ≤ ((19883779571490990987/19885000000000000000 : ℝ)+2*(265082878761/795400000000000 : ℝ)*(17547/100000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (19883779571490990987/19885000000000000000 : ℝ)+2*(265082878761/795400000000000 : ℝ)*(17547/100000 : ℝ)=(10000555834110033/10000000000000000 : ℝ) by norm_num, show 1+2*(14154563568128367/100000000000000000000 : ℝ)=(50014154563568128367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19883779571490990987/19885000000000000000 : ℝ)*(X 1 0+X 2 0)+(265082878761/795400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (9593/100000 : ℝ)) (hi := (17547/100000 : ℝ)) (c := (19883779571490990987/19885000000000000000 : ℝ)) (alpha := (265082878761/795400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19883779571490990987/19885000000000000000 : ℝ)*(X 0 1+X 2 1)+(265082878761/795400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (9593/100000 : ℝ)) (hi := (17547/100000 : ℝ)) (c := (19883779571490990987/19885000000000000000 : ℝ)) (alpha := (265082878761/795400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19883779571490990987/19885000000000000000 : ℝ)*(X 0 2+X 1 2)+(265082878761/795400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (9593/100000 : ℝ)) (hi := (17547/100000 : ℝ)) (c := (19883779571490990987/19885000000000000000 : ℝ)) (alpha := (265082878761/795400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1448844943/10000000000 : ℝ)*X 0 0+(5477275621/10000000000 : ℝ)*X 0 1+(128407563/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347083069/10000000000 : ℝ)*X 1 0+(-1625825763/10000000000 : ℝ)*X 1 1+(642037859/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347082767/10000000000 : ℝ)*X 2 0+(2568151447/5000000000 : ℝ)*X 2 1+(-1625826139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2058809909/5000000000 : ℝ)*X 0 0+(365300119/1000000000 : ℝ)*X 0 1+(2309520177/5000000000 : ℝ)*X 0 2+(2058809909/5000000000 : ℝ)*X 1 0+(365300119/1000000000 : ℝ)*X 1 1+(2309520177/5000000000 : ℝ)*X 1 2+(2058809909/5000000000 : ℝ)*X 2 0+(365300119/1000000000 : ℝ)*X 2 1+(2309520177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1449002617/10000000000 : ℝ)*X 0 0+(5140061171/10000000000 : ℝ)*X 0 1+(5473460767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5255849859/10000000000 : ℝ)*X 1 0+(-161083513/1250000000 : ℝ)*X 1 1+(171045649/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255849853/10000000000 : ℝ)*X 2 0+(1368365193/2500000000 : ℝ)*X 2 1+(-644334053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4118066731/10000000000 : ℝ)*X 0 0+(4608391971/10000000000 : ℝ)*X 0 1+(1831904711/5000000000 : ℝ)*X 0 2+(4118066731/10000000000 : ℝ)*X 1 0+(4608391971/10000000000 : ℝ)*X 1 1+(1831904711/5000000000 : ℝ)*X 1 2+(4118066731/10000000000 : ℝ)*X 2 0+(4608391971/10000000000 : ℝ)*X 2 1+(1831904711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5018876140578494600966265423/994250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (992498291/100000000000000 : ℝ)*(base19) + (202774559/25000000000000 : ℝ)*(base23) + (2106349/25000000000000 : ℝ)*(lower2) + (279290083/100000000000000 : ℝ)*(upper3) + (11582371/100000000000000 : ℝ)*(upper5) + (1983984363912143/100000000000000 : ℝ)*(major0) + (1983984363912143/100000000000000 : ℝ)*(major1) + (1983984363912143/100000000000000 : ℝ)*(major2) + (366599626503501/12500000000000 : ℝ)*(sp0) + (2932805115134047/100000000000000 : ℝ)*(sp1) + (1466402648267051/50000000000000 : ℝ)*(sp2) + (1035157872747529/100000000000000 : ℝ)*(sp3) + (9095604331/100000000000000 : ℝ)*(sp4) + (1144795257/25000000000000 : ℝ)*(sp7) + (1035162451928557/100000000000000 : ℝ)*(f.failure) + (1466403053816169/50000000000000 : ℝ)*(f.sum) + (52497952561193/39770000000000000000000000000 : ℝ)*base65 + (16955275705286069859/1988500000000000000000000000000000 : ℝ)*base68 + (14063564906488069859/1988500000000000000000000000000000 : ℝ)*base70 + (3141462821877069859/1988500000000000000000000000000000 : ℝ)*base72 + (130953955232667/39770000000000000000000000000 : ℝ)*base74 + (4655535890402430141/1988500000000000000000000000000000 : ℝ)*base75 + (9609794798980569859/1988500000000000000000000000000000 : ℝ)*base78 + (11416310972832430141/1988500000000000000000000000000000 : ℝ)*base79 + (99619413517257/39770000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11443499/2500000000000000000000 : ℝ)*base89 + (11443499/2500000000000000000000 : ℝ)*base91 + (11443499/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1497375696502597961320164009/248562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (824464683/100000000000000 : ℝ)*(base19) + (223454149/25000000000000 : ℝ)*(base23) + (126041169/100000000000000 : ℝ)*(upper3) + (8299791/25000000000000 : ℝ)*(lower4) + (126540331/100000000000000 : ℝ)*(upper5) + (507259020000269/25000000000000 : ℝ)*(major0) + (507259020000269/25000000000000 : ℝ)*(major1) + (507259020000269/25000000000000 : ℝ)*(major2) + (733946759/10000000000000 : ℝ)*(sp1) + (986638447/12500000000000 : ℝ)*(sp2) + (749850837951981/25000000000000 : ℝ)*(sp4) + (2999395187875651/100000000000000 : ℝ)*(sp5) + (374924320610469/12500000000000 : ℝ)*(sp6) + (211733721477901/20000000000000 : ℝ)*(sp7) + (211733721477901/20000000000000 : ℝ)*(f.failure) + (749850837951981/25000000000000 : ℝ)*(f.sum) + (78181094246177/19885000000000000000000000000 : ℝ)*base66 + (844746278641425503/497125000000000000000000000000000 : ℝ)*base67 + (2797315980788949497/497125000000000000000000000000000 : ℝ)*base70 + (2341969990177949497/497125000000000000000000000000000 : ℝ)*base72 + (23580663013733/19885000000000000000000000000 : ℝ)*base73 + (781554013661449497/497125000000000000000000000000000 : ℝ)*base76 + (2260896025982074497/497125000000000000000000000000000 : ℝ)*base78 + (1952448911282925503/497125000000000000000000000000000 : ℝ)*base79 + (1823881756707/4971250000000000000000000000 : ℝ)*base81 + (1180107/500000000000000000000 : ℝ)*base89 + (1180107/500000000000000000000 : ℝ)*base91 + (1180107/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1700_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (859/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1700_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1700_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (859/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1700_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1700_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1700_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (859/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1700_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
