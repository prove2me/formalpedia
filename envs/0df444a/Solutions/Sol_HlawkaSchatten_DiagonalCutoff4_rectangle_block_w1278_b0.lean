-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:51.089685+00:00
-- url     : https://prove2.me/submissions/24cf33da-d77d-471c-804d-323dc86f8de0

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
theorem support_rectangle_w1278_s0_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-184759399/1000000000 : ℝ)*x 0 + (1506254981/2500000000 : ℝ)*x 1 + (2397705749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (184759399/1000000000 : ℝ)^2119 ≤ (10788049048293/100000000000000 : ℝ)^1607 := by
    have hnat : (184759399 : ℕ)^2119*100000000000000^1607 ≤ 10788049048293^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184759399 1000000000 10788049048293 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506254981/2500000000 : ℝ)^2119 ≤ (3204290903983/6250000000000 : ℝ)^1607 := by
    have hnat : (1506254981 : ℕ)^2119*6250000000000^1607 ≤ 3204290903983^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506254981 2500000000 3204290903983 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397705749/5000000000 : ℝ)^2119 ≤ (4742912059619/12500000000000 : ℝ)^1607 := by
    have hnat : (2397705749 : ℕ)^2119*12500000000000^1607 ≤ 4742912059619^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397705749 5000000000 4742912059619 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-184759399/1000000000 : ℝ), (1506254981/2500000000 : ℝ), (2397705749/5000000000 : ℝ)] ![(10788049048293/100000000000000 : ℝ), (3204290903983/6250000000000 : ℝ), (4742912059619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-184759399/1000000000 : ℝ)|^2119 ≤ (10788049048293/100000000000000 : ℝ)^1607
        have hw : |(-184759399/1000000000 : ℝ)|=(184759399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506254981/2500000000 : ℝ)|^2119 ≤ (3204290903983/6250000000000 : ℝ)^1607
        have hw : |(1506254981/2500000000 : ℝ)|=(1506254981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397705749/5000000000 : ℝ)|^2119 ≤ (4742912059619/12500000000000 : ℝ)^1607
        have hw : |(2397705749/5000000000 : ℝ)|=(2397705749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1101798013/2000000000 : ℝ)*x 0 + (-2549814633/10000000000 : ℝ)*x 1 + (4795411473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101798013/2000000000 : ℝ)^2119 ≤ (22779592469571/50000000000000 : ℝ)^1607 := by
    have hnat : (1101798013 : ℕ)^2119*50000000000000^1607 ≤ 22779592469571^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101798013 2000000000 22779592469571 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549814633/10000000000 : ℝ)^2119 ≤ (16497518829423/100000000000000 : ℝ)^1607 := by
    have hnat : (2549814633 : ℕ)^2119*100000000000000^1607 ≤ 16497518829423^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549814633 10000000000 16497518829423 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795411473/10000000000 : ℝ)^2119 ≤ (18971648108059/50000000000000 : ℝ)^1607 := by
    have hnat : (4795411473 : ℕ)^2119*50000000000000^1607 ≤ 18971648108059^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795411473 10000000000 18971648108059 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101798013/2000000000 : ℝ), (-2549814633/10000000000 : ℝ), (4795411473/10000000000 : ℝ)] ![(22779592469571/50000000000000 : ℝ), (16497518829423/100000000000000 : ℝ), (18971648108059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101798013/2000000000 : ℝ)|^2119 ≤ (22779592469571/50000000000000 : ℝ)^1607
        have hw : |(1101798013/2000000000 : ℝ)|=(1101798013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2549814633/10000000000 : ℝ)|^2119 ≤ (16497518829423/100000000000000 : ℝ)^1607
        have hw : |(-2549814633/10000000000 : ℝ)|=(2549814633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795411473/10000000000 : ℝ)|^2119 ≤ (18971648108059/50000000000000 : ℝ)^1607
        have hw : |(4795411473/10000000000 : ℝ)|=(4795411473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5508990083/10000000000 : ℝ)*x 0 + (299713217/625000000 : ℝ)*x 1 + (-254981461/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508990083/10000000000 : ℝ)^2119 ≤ (45559185135429/100000000000000 : ℝ)^1607 := by
    have hnat : (5508990083 : ℕ)^2119*100000000000000^1607 ≤ 45559185135429^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508990083 10000000000 45559185135429 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299713217/625000000 : ℝ)^2119 ≤ (7588659241137/20000000000000 : ℝ)^1607 := by
    have hnat : (299713217 : ℕ)^2119*20000000000000^1607 ≤ 7588659241137^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299713217 625000000 7588659241137 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254981461/1000000000 : ℝ)^2119 ≤ (16497518633199/100000000000000 : ℝ)^1607 := by
    have hnat : (254981461 : ℕ)^2119*100000000000000^1607 ≤ 16497518633199^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254981461 1000000000 16497518633199 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508990083/10000000000 : ℝ), (299713217/625000000 : ℝ), (-254981461/1000000000 : ℝ)] ![(45559185135429/100000000000000 : ℝ), (7588659241137/20000000000000 : ℝ), (16497518633199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508990083/10000000000 : ℝ)|^2119 ≤ (45559185135429/100000000000000 : ℝ)^1607
        have hw : |(5508990083/10000000000 : ℝ)|=(5508990083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299713217/625000000 : ℝ)|^2119 ≤ (7588659241137/20000000000000 : ℝ)^1607
        have hw : |(299713217/625000000 : ℝ)|=(299713217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254981461/1000000000 : ℝ)|^2119 ≤ (16497518633199/100000000000000 : ℝ)^1607
        have hw : |(-254981461/1000000000 : ℝ)|=(254981461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (418849221/1000000000 : ℝ)*x 0 + (777595143/2500000000 : ℝ)*x 1 + (5624005301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418849221/1000000000 : ℝ)^2119 ≤ (31742636388711/100000000000000 : ℝ)^1607 := by
    have hnat : (418849221 : ℕ)^2119*100000000000000^1607 ≤ 31742636388711^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418849221 1000000000 31742636388711 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777595143/2500000000 : ℝ)^2119 ≤ (21439804871559/100000000000000 : ℝ)^1607 := by
    have hnat : (777595143 : ℕ)^2119*100000000000000^1607 ≤ 21439804871559^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777595143 2500000000 21439804871559 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5624005301/10000000000 : ℝ)^2119 ≤ (46817558722491/100000000000000 : ℝ)^1607 := by
    have hnat : (5624005301 : ℕ)^2119*100000000000000^1607 ≤ 46817558722491^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624005301 10000000000 46817558722491 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418849221/1000000000 : ℝ), (777595143/2500000000 : ℝ), (5624005301/10000000000 : ℝ)] ![(31742636388711/100000000000000 : ℝ), (21439804871559/100000000000000 : ℝ), (46817558722491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418849221/1000000000 : ℝ)|^2119 ≤ (31742636388711/100000000000000 : ℝ)^1607
        have hw : |(418849221/1000000000 : ℝ)|=(418849221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777595143/2500000000 : ℝ)|^2119 ≤ (21439804871559/100000000000000 : ℝ)^1607
        have hw : |(777595143/2500000000 : ℝ)|=(777595143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5624005301/10000000000 : ℝ)|^2119 ≤ (46817558722491/100000000000000 : ℝ)^1607
        have hw : |(5624005301/10000000000 : ℝ)|=(5624005301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852395531/10000000000 : ℝ)*x 0 + (1206791843/2500000000 : ℝ)*x 1 + (2996067839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852395531/10000000000 : ℝ)^2119 ≤ (5412516433301/50000000000000 : ℝ)^1607 := by
    have hnat : (1852395531 : ℕ)^2119*50000000000000^1607 ≤ 5412516433301^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852395531 10000000000 5412516433301 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206791843/2500000000 : ℝ)^2119 ≤ (38274965987559/100000000000000 : ℝ)^1607 := by
    have hnat : (1206791843 : ℕ)^2119*100000000000000^1607 ≤ 38274965987559^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206791843 2500000000 38274965987559 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996067839/5000000000 : ℝ)^2119 ≤ (2036000045333/4000000000000 : ℝ)^1607 := by
    have hnat : (2996067839 : ℕ)^2119*4000000000000^1607 ≤ 2036000045333^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996067839 5000000000 2036000045333 4000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852395531/10000000000 : ℝ), (1206791843/2500000000 : ℝ), (2996067839/5000000000 : ℝ)] ![(5412516433301/50000000000000 : ℝ), (38274965987559/100000000000000 : ℝ), (2036000045333/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852395531/10000000000 : ℝ)|^2119 ≤ (5412516433301/50000000000000 : ℝ)^1607
        have hw : |(-1852395531/10000000000 : ℝ)|=(1852395531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206791843/2500000000 : ℝ)|^2119 ≤ (38274965987559/100000000000000 : ℝ)^1607
        have hw : |(1206791843/2500000000 : ℝ)|=(1206791843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996067839/5000000000 : ℝ)|^2119 ≤ (2036000045333/4000000000000 : ℝ)^1607
        have hw : |(2996067839/5000000000 : ℝ)|=(2996067839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587173379/5000000000 : ℝ)*x 0 + (-1353088033/10000000000 : ℝ)*x 1 + (5992138149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587173379/5000000000 : ℝ)^2119 ≤ (20972884279087/50000000000000 : ℝ)^1607 := by
    have hnat : (2587173379 : ℕ)^2119*50000000000000^1607 ≤ 20972884279087^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587173379 5000000000 20972884279087 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353088033/10000000000 : ℝ)^2119 ≤ (1788550655523/25000000000000 : ℝ)^1607 := by
    have hnat : (1353088033 : ℕ)^2119*25000000000000^1607 ≤ 1788550655523^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353088033 10000000000 1788550655523 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5992138149/10000000000 : ℝ)^2119 ≤ (50900028810643/100000000000000 : ℝ)^1607 := by
    have hnat : (5992138149 : ℕ)^2119*100000000000000^1607 ≤ 50900028810643^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992138149 10000000000 50900028810643 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587173379/5000000000 : ℝ), (-1353088033/10000000000 : ℝ), (5992138149/10000000000 : ℝ)] ![(20972884279087/50000000000000 : ℝ), (1788550655523/25000000000000 : ℝ), (50900028810643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587173379/5000000000 : ℝ)|^2119 ≤ (20972884279087/50000000000000 : ℝ)^1607
        have hw : |(2587173379/5000000000 : ℝ)|=(2587173379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1353088033/10000000000 : ℝ)|^2119 ≤ (1788550655523/25000000000000 : ℝ)^1607
        have hw : |(-1353088033/10000000000 : ℝ)|=(1353088033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5992138149/10000000000 : ℝ)|^2119 ≤ (50900028810643/100000000000000 : ℝ)^1607
        have hw : |(5992138149/10000000000 : ℝ)|=(5992138149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1034869587/2000000000 : ℝ)*x 0 + (5992136097/10000000000 : ℝ)*x 1 + (-54123581/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034869587/2000000000 : ℝ)^2119 ≤ (10486445284859/25000000000000 : ℝ)^1607 := by
    have hnat : (1034869587 : ℕ)^2119*25000000000000^1607 ≤ 10486445284859^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034869587 2000000000 10486445284859 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5992136097/10000000000 : ℝ)^2119 ≤ (12725001456621/25000000000000 : ℝ)^1607 := by
    have hnat : (5992136097 : ℕ)^2119*25000000000000^1607 ≤ 12725001456621^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992136097 10000000000 12725001456621 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54123581/400000000 : ℝ)^2119 ≤ (1788553256037/25000000000000 : ℝ)^1607 := by
    have hnat : (54123581 : ℕ)^2119*25000000000000^1607 ≤ 1788553256037^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54123581 400000000 1788553256037 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034869587/2000000000 : ℝ), (5992136097/10000000000 : ℝ), (-54123581/400000000 : ℝ)] ![(10486445284859/25000000000000 : ℝ), (12725001456621/25000000000000 : ℝ), (1788553256037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034869587/2000000000 : ℝ)|^2119 ≤ (10486445284859/25000000000000 : ℝ)^1607
        have hw : |(1034869587/2000000000 : ℝ)|=(1034869587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5992136097/10000000000 : ℝ)|^2119 ≤ (12725001456621/25000000000000 : ℝ)^1607
        have hw : |(5992136097/10000000000 : ℝ)|=(5992136097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54123581/400000000 : ℝ)|^2119 ≤ (1788553256037/25000000000000 : ℝ)^1607
        have hw : |(-54123581/400000000 : ℝ)|=(54123581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s0_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (524788927/1250000000 : ℝ)*x 0 + (1389773689/2500000000 : ℝ)*x 1 + (794399457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524788927/1250000000 : ℝ)^2119 ≤ (31840797351203/100000000000000 : ℝ)^1607 := by
    have hnat : (524788927 : ℕ)^2119*100000000000000^1607 ≤ 31840797351203^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524788927 1250000000 31840797351203 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389773689/2500000000 : ℝ)^2119 ≤ (46106358260387/100000000000000 : ℝ)^1607 := by
    have hnat : (1389773689 : ℕ)^2119*100000000000000^1607 ≤ 46106358260387^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389773689 2500000000 46106358260387 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794399457/2500000000 : ℝ)^2119 ≤ (441056887483/2000000000000 : ℝ)^1607 := by
    have hnat : (794399457 : ℕ)^2119*2000000000000^1607 ≤ 441056887483^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794399457 2500000000 441056887483 2000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524788927/1250000000 : ℝ), (1389773689/2500000000 : ℝ), (794399457/2500000000 : ℝ)] ![(31840797351203/100000000000000 : ℝ), (46106358260387/100000000000000 : ℝ), (441056887483/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524788927/1250000000 : ℝ)|^2119 ≤ (31840797351203/100000000000000 : ℝ)^1607
        have hw : |(524788927/1250000000 : ℝ)|=(524788927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1389773689/2500000000 : ℝ)|^2119 ≤ (46106358260387/100000000000000 : ℝ)^1607
        have hw : |(1389773689/2500000000 : ℝ)|=(1389773689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(794399457/2500000000 : ℝ)|^2119 ≤ (441056887483/2000000000000 : ℝ)^1607
        have hw : |(794399457/2500000000 : ℝ)|=(794399457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (923/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27339/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4237/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4237 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4237*1^1024 ≤ 0^1024*1^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4237/1024 : ℝ) ≤ (141034547284335417/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4237 ≤ (141034547284335417/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4237*6250000000000000000^1024 ≤ 141034547284335417^1024*5^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 141034547284335417 6250000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (141034547284335417/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4237 := by
      have hnat : (1 : ℕ)^1024*1^4237 ≤ 1^4237*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6391034547284335417/6250000000000000000 : ℝ) ≤ (5027037965568023/5000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (6391034547284335417/6250000000000000000 : ℝ)^1024 ≤ (5027037965568023/5000000000000000 : ℝ)^4237 := by
      have hnat : (6391034547284335417 : ℕ)^1024*5000000000000000^4237 ≤ 5027037965568023^4237*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6391034547284335417 6250000000000000000 5027037965568023 5000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027037965568023/5000000000000000 : ℝ)) (X := (6391034547284335417/6250000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3266034547284335417/3125000000000000000 : ℝ) ≤ (2527037965568023/2500000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (3266034547284335417/3125000000000000000 : ℝ)^1024 ≤ (2527037965568023/2500000000000000 : ℝ)^4237 := by
      have hnat : (3266034547284335417 : ℕ)^1024*2500000000000000^4237 ≤ 2527037965568023^4237*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3266034547284335417 3125000000000000000 2527037965568023 2500000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527037965568023/2500000000000000 : ℝ)) (X := (3266034547284335417/3125000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27037965568023/2000000000000000 : ℝ)*(0 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27037965568023/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(141034547284335417/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27037965568023/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27037965568023/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027037965568023/5000000000000000 : ℝ) by norm_num, show 1+(141034547284335417/6250000000000000000 : ℝ)+(0 : ℝ)=(6391034547284335417/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(141034547284335417/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27037965568023/2000000000000000 : ℝ)*(2/5 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27037965568023/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527037965568023/2500000000000000 : ℝ) by norm_num, show 1+2*(141034547284335417/6250000000000000000 : ℝ)=(3266034547284335417/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27037965568023/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27037965568023/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27037965568023/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27037965568023/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27037965568023/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27037965568023/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-184759399/1000000000 : ℝ)*X 0 0+(1506254981/2500000000 : ℝ)*X 0 1+(2397705749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1101798013/2000000000 : ℝ)*X 1 0+(-2549814633/10000000000 : ℝ)*X 1 1+(4795411473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5508990083/10000000000 : ℝ)*X 2 0+(299713217/625000000 : ℝ)*X 2 1+(-254981461/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((418849221/1000000000 : ℝ)*X 0 0+(777595143/2500000000 : ℝ)*X 0 1+(5624005301/10000000000 : ℝ)*X 0 2+(418849221/1000000000 : ℝ)*X 1 0+(777595143/2500000000 : ℝ)*X 1 1+(5624005301/10000000000 : ℝ)*X 1 2+(418849221/1000000000 : ℝ)*X 2 0+(777595143/2500000000 : ℝ)*X 2 1+(5624005301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1852395531/10000000000 : ℝ)*X 0 0+(1206791843/2500000000 : ℝ)*X 0 1+(2996067839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587173379/5000000000 : ℝ)*X 1 0+(-1353088033/10000000000 : ℝ)*X 1 1+(5992138149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034869587/2000000000 : ℝ)*X 2 0+(5992136097/10000000000 : ℝ)*X 2 1+(-54123581/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524788927/1250000000 : ℝ)*X 0 0+(1389773689/2500000000 : ℝ)*X 0 1+(794399457/2500000000 : ℝ)*X 0 2+(524788927/1250000000 : ℝ)*X 1 0+(1389773689/2500000000 : ℝ)*X 1 1+(794399457/2500000000 : ℝ)*X 1 2+(524788927/1250000000 : ℝ)*X 2 0+(1389773689/2500000000 : ℝ)*X 2 1+(794399457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (228532630914718263780777/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13161289/25000000000000 : ℝ)*(base1) + (1109751247/100000000000000 : ℝ)*(base19) + (1112408523/100000000000000 : ℝ)*(base23) + (126540133/100000000000000 : ℝ)*(upper3) + (66478199/50000000000000 : ℝ)*(upper5) + (605554617100489/100000000000000 : ℝ)*(major0) + (605554617100489/100000000000000 : ℝ)*(major1) + (605554617100489/100000000000000 : ℝ)*(major2) + (813270349219723/100000000000000 : ℝ)*(sp0) + (81327272783161/10000000000000 : ℝ)*(sp1) + (406636362587167/50000000000000 : ℝ)*(sp2) + (397833488486487/100000000000000 : ℝ)*(sp3) + (354100829/10000000000000 : ℝ)*(sp4) + (1703131381/100000000000000 : ℝ)*(sp7) + (24864702766439/6250000000000 : ℝ)*(f.failure) + (813273837582857/100000000000000 : ℝ)*(f.sum) + (147764655463247/100000000000000000000000000000 : ℝ)*base65 + (1944585449663247/200000000000000000000000000000 : ℝ)*base67 + (1168443410263247/200000000000000000000000000000 : ℝ)*base69 + (1618760872863247/200000000000000000000000000000 : ℝ)*base71 + (552582209063247/100000000000000000000000000000 : ℝ)*base73 + (488300239063247/200000000000000000000000000000 : ℝ)*base75 + (1224925858463247/200000000000000000000000000000 : ℝ)*base77 + (1131528506463247/200000000000000000000000000000 : ℝ)*base79 + (294445324563247/100000000000000000000000000000 : ℝ)*base81 + (6175571/625000000000000000000 : ℝ)*base90 + (6175571/625000000000000000000 : ℝ)*base92 + (6175571/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76332790156847274734241/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40341719/12500000000000 : ℝ)*(base1) + (1214489231/100000000000000 : ℝ)*(base19) + (1395152843/100000000000000 : ℝ)*(base23) + (255593329/100000000000000 : ℝ)*(upper3) + (319574040709011/50000000000000 : ℝ)*(major0) + (319574040709011/50000000000000 : ℝ)*(major1) + (319574040709011/50000000000000 : ℝ)*(major2) + (2088021057/100000000000000 : ℝ)*(sp1) + (931195263/50000000000000 : ℝ)*(sp2) + (159497537/100000000000000 : ℝ)*(sp3) + (429195458037059/50000000000000 : ℝ)*(sp4) + (429193645415039/50000000000000 : ℝ)*(sp5) + (214596833949249/25000000000000 : ℝ)*(sp6) + (419904883710271/100000000000000 : ℝ)*(sp7) + (10497634148539/2500000000000 : ℝ)*(f.failure) + (429195296670183/50000000000000 : ℝ)*(f.sum) + (111604577155253/50000000000000000000000000000 : ℝ)*base65 + (774991475955253/100000000000000000000000000000 : ℝ)*base67 + (274376566655253/100000000000000000000000000000 : ℝ)*base69 + (1203285636055253/100000000000000000000000000000 : ℝ)*base71 + (51072950305253/50000000000000000000000000000 : ℝ)*base73 + (804011508755253/100000000000000000000000000000 : ℝ)*base75 + (1154588527155253/100000000000000000000000000000 : ℝ)*base77 + (1677291377155253/100000000000000000000000000000 : ℝ)*base79 + (168115893694747/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1682471/250000000000000000000 : ℝ)*base90 + (1682471/250000000000000000000 : ℝ)*base92 + (1682471/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1278_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_s1_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-10208319/50000000 : ℝ)*x 0 + (1418019511/2500000000 : ℝ)*x 1 + (5024112623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10208319/50000000 : ℝ)^2119 ≤ (12306682483641/100000000000000 : ℝ)^1607 := by
    have hnat : (10208319 : ℕ)^2119*100000000000000^1607 ≤ 12306682483641^1607*50000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10208319 50000000 12306682483641 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418019511/2500000000 : ℝ)^2119 ≤ (5918245455549/12500000000000 : ℝ)^1607 := by
    have hnat : (1418019511 : ℕ)^2119*12500000000000^1607 ≤ 5918245455549^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418019511 2500000000 5918245455549 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5024112623/10000000000 : ℝ)^2119 ≤ (20173676930097/50000000000000 : ℝ)^1607 := by
    have hnat : (5024112623 : ℕ)^2119*50000000000000^1607 ≤ 20173676930097^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024112623 10000000000 20173676930097 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10208319/50000000 : ℝ), (1418019511/2500000000 : ℝ), (5024112623/10000000000 : ℝ)] ![(12306682483641/100000000000000 : ℝ), (5918245455549/12500000000000 : ℝ), (20173676930097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10208319/50000000 : ℝ)|^2119 ≤ (12306682483641/100000000000000 : ℝ)^1607
        have hw : |(-10208319/50000000 : ℝ)|=(10208319/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418019511/2500000000 : ℝ)|^2119 ≤ (5918245455549/12500000000000 : ℝ)^1607
        have hw : |(1418019511/2500000000 : ℝ)|=(1418019511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5024112623/10000000000 : ℝ)|^2119 ≤ (20173676930097/50000000000000 : ℝ)^1607
        have hw : |(5024112623/10000000000 : ℝ)|=(5024112623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5412478427/10000000000 : ℝ)*x 0 + (-298676459/1250000000 : ℝ)*x 1 + (1004822493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412478427/10000000000 : ℝ)^2119 ≤ (2225484527767/5000000000000 : ℝ)^1607 := by
    have hnat : (5412478427 : ℕ)^2119*5000000000000^1607 ≤ 2225484527767^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412478427 10000000000 2225484527767 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298676459/1250000000 : ℝ)^2119 ≤ (15142957238129/100000000000000 : ℝ)^1607 := by
    have hnat : (298676459 : ℕ)^2119*100000000000000^1607 ≤ 15142957238129^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298676459 1250000000 15142957238129 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004822493/2000000000 : ℝ)^2119 ≤ (40347352187071/100000000000000 : ℝ)^1607 := by
    have hnat : (1004822493 : ℕ)^2119*100000000000000^1607 ≤ 40347352187071^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004822493 2000000000 40347352187071 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412478427/10000000000 : ℝ), (-298676459/1250000000 : ℝ), (1004822493/2000000000 : ℝ)] ![(2225484527767/5000000000000 : ℝ), (15142957238129/100000000000000 : ℝ), (40347352187071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412478427/10000000000 : ℝ)|^2119 ≤ (2225484527767/5000000000000 : ℝ)^1607
        have hw : |(5412478427/10000000000 : ℝ)|=(5412478427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-298676459/1250000000 : ℝ)|^2119 ≤ (15142957238129/100000000000000 : ℝ)^1607
        have hw : |(-298676459/1250000000 : ℝ)|=(298676459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004822493/2000000000 : ℝ)|^2119 ≤ (40347352187071/100000000000000 : ℝ)^1607
        have hw : |(1004822493/2000000000 : ℝ)|=(1004822493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2706239119/5000000000 : ℝ)*x 0 + (2512056313/5000000000 : ℝ)*x 1 + (-2389411713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706239119/5000000000 : ℝ)^2119 ≤ (445096885059/1000000000000 : ℝ)^1607 := by
    have hnat : (2706239119 : ℕ)^2119*1000000000000^1607 ≤ 445096885059^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706239119 5000000000 445096885059 1000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512056313/5000000000 : ℝ)^2119 ≤ (20173676945981/50000000000000 : ℝ)^1607 := by
    have hnat : (2512056313 : ℕ)^2119*50000000000000^1607 ≤ 20173676945981^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512056313 5000000000 20173676945981 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389411713/10000000000 : ℝ)^2119 ≤ (15142957580753/100000000000000 : ℝ)^1607 := by
    have hnat : (2389411713 : ℕ)^2119*100000000000000^1607 ≤ 15142957580753^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389411713 10000000000 15142957580753 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706239119/5000000000 : ℝ), (2512056313/5000000000 : ℝ), (-2389411713/10000000000 : ℝ)] ![(445096885059/1000000000000 : ℝ), (20173676945981/50000000000000 : ℝ), (15142957580753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706239119/5000000000 : ℝ)|^2119 ≤ (445096885059/1000000000000 : ℝ)^1607
        have hw : |(2706239119/5000000000 : ℝ)|=(2706239119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512056313/5000000000 : ℝ)|^2119 ≤ (20173676945981/50000000000000 : ℝ)^1607
        have hw : |(2512056313/5000000000 : ℝ)|=(2512056313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2389411713/10000000000 : ℝ)|^2119 ≤ (15142957580753/100000000000000 : ℝ)^1607
        have hw : |(-2389411713/10000000000 : ℝ)|=(2389411713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53794801/125000000 : ℝ)*x 0 + (737972979/2000000000 : ℝ)*x 1 + (78351047/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53794801/125000000 : ℝ)^2119 ≤ (32897764728987/100000000000000 : ℝ)^1607 := by
    have hnat : (53794801 : ℕ)^2119*100000000000000^1607 ≤ 32897764728987^1607*125000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53794801 125000000 32897764728987 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737972979/2000000000 : ℝ)^2119 ≤ (167856195527/625000000000 : ℝ)^1607 := by
    have hnat : (737972979 : ℕ)^2119*625000000000^1607 ≤ 167856195527^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737972979 2000000000 167856195527 625000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78351047/156250000 : ℝ)^2119 ≤ (40245243974217/100000000000000 : ℝ)^1607 := by
    have hnat : (78351047 : ℕ)^2119*100000000000000^1607 ≤ 40245243974217^1607*156250000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78351047 156250000 40245243974217 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53794801/125000000 : ℝ), (737972979/2000000000 : ℝ), (78351047/156250000 : ℝ)] ![(32897764728987/100000000000000 : ℝ), (167856195527/625000000000 : ℝ), (40245243974217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53794801/125000000 : ℝ)|^2119 ≤ (32897764728987/100000000000000 : ℝ)^1607
        have hw : |(53794801/125000000 : ℝ)|=(53794801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737972979/2000000000 : ℝ)|^2119 ≤ (167856195527/625000000000 : ℝ)^1607
        have hw : |(737972979/2000000000 : ℝ)|=(737972979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78351047/156250000 : ℝ)|^2119 ≤ (40245243974217/100000000000000 : ℝ)^1607
        have hw : |(78351047/156250000 : ℝ)|=(78351047/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51058299/250000000 : ℝ)*x 0 + (5032650847/10000000000 : ℝ)*x 1 + (1132675329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51058299/250000000 : ℝ)^2119 ≤ (492479738689/4000000000000 : ℝ)^1607 := by
    have hnat : (51058299 : ℕ)^2119*4000000000000^1607 ≤ 492479738689^1607*250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51058299 250000000 492479738689 4000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032650847/10000000000 : ℝ)^2119 ≤ (20218896438203/50000000000000 : ℝ)^1607 := by
    have hnat : (5032650847 : ℕ)^2119*50000000000000^1607 ≤ 20218896438203^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032650847 10000000000 20218896438203 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132675329/2000000000 : ℝ)^2119 ≤ (47250213653397/100000000000000 : ℝ)^1607 := by
    have hnat : (1132675329 : ℕ)^2119*100000000000000^1607 ≤ 47250213653397^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132675329 2000000000 47250213653397 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51058299/250000000 : ℝ), (5032650847/10000000000 : ℝ), (1132675329/2000000000 : ℝ)] ![(492479738689/4000000000000 : ℝ), (20218896438203/50000000000000 : ℝ), (47250213653397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51058299/250000000 : ℝ)|^2119 ≤ (492479738689/4000000000000 : ℝ)^1607
        have hw : |(-51058299/250000000 : ℝ)|=(51058299/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032650847/10000000000 : ℝ)|^2119 ≤ (20218896438203/50000000000000 : ℝ)^1607
        have hw : |(5032650847/10000000000 : ℝ)|=(5032650847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132675329/2000000000 : ℝ)|^2119 ≤ (47250213653397/100000000000000 : ℝ)^1607
        have hw : |(1132675329/2000000000 : ℝ)|=(1132675329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5245278097/10000000000 : ℝ)*x 0 + (-1750147441/10000000000 : ℝ)*x 1 + (566337701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245278097/10000000000 : ℝ)^2119 ≤ (21352811406921/50000000000000 : ℝ)^1607 := by
    have hnat : (5245278097 : ℕ)^2119*50000000000000^1607 ≤ 21352811406921^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278097 10000000000 21352811406921 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1750147441/10000000000 : ℝ)^2119 ≤ (5022079751899/50000000000000 : ℝ)^1607 := by
    have hnat : (1750147441 : ℕ)^2119*50000000000000^1607 ≤ 5022079751899^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750147441 10000000000 5022079751899 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566337701/1000000000 : ℝ)^2119 ≤ (23625108834433/50000000000000 : ℝ)^1607 := by
    have hnat : (566337701 : ℕ)^2119*50000000000000^1607 ≤ 23625108834433^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566337701 1000000000 23625108834433 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245278097/10000000000 : ℝ), (-1750147441/10000000000 : ℝ), (566337701/1000000000 : ℝ)] ![(21352811406921/50000000000000 : ℝ), (5022079751899/50000000000000 : ℝ), (23625108834433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245278097/10000000000 : ℝ)|^2119 ≤ (21352811406921/50000000000000 : ℝ)^1607
        have hw : |(5245278097/10000000000 : ℝ)|=(5245278097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1750147441/10000000000 : ℝ)|^2119 ≤ (5022079751899/50000000000000 : ℝ)^1607
        have hw : |(-1750147441/10000000000 : ℝ)|=(1750147441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566337701/1000000000 : ℝ)|^2119 ≤ (23625108834433/50000000000000 : ℝ)^1607
        have hw : |(566337701/1000000000 : ℝ)|=(566337701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5245278011/10000000000 : ℝ)*x 0 + (5663376733/10000000000 : ℝ)*x 1 + (-875073983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245278011/10000000000 : ℝ)^2119 ≤ (42705621890569/100000000000000 : ℝ)^1607 := by
    have hnat : (5245278011 : ℕ)^2119*100000000000000^1607 ≤ 42705621890569^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245278011 10000000000 42705621890569 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663376733/10000000000 : ℝ)^2119 ≤ (4725021462151/10000000000000 : ℝ)^1607 := by
    have hnat : (5663376733 : ℕ)^2119*10000000000000^1607 ≤ 4725021462151^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663376733 10000000000 4725021462151 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875073983/5000000000 : ℝ)^2119 ≤ (40176653907/400000000000 : ℝ)^1607 := by
    have hnat : (875073983 : ℕ)^2119*400000000000^1607 ≤ 40176653907^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875073983 5000000000 40176653907 400000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245278011/10000000000 : ℝ), (5663376733/10000000000 : ℝ), (-875073983/5000000000 : ℝ)] ![(42705621890569/100000000000000 : ℝ), (4725021462151/10000000000000 : ℝ), (40176653907/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245278011/10000000000 : ℝ)|^2119 ≤ (42705621890569/100000000000000 : ℝ)^1607
        have hw : |(5245278011/10000000000 : ℝ)|=(5245278011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663376733/10000000000 : ℝ)|^2119 ≤ (4725021462151/10000000000000 : ℝ)^1607
        have hw : |(5663376733/10000000000 : ℝ)|=(5663376733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-875073983/5000000000 : ℝ)|^2119 ≤ (40176653907/400000000000 : ℝ)^1607
        have hw : |(-875073983/5000000000 : ℝ)|=(875073983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s1_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2152474799/5000000000 : ℝ)*x 0 + (4997012887/10000000000 : ℝ)*x 1 + (3707652391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152474799/5000000000 : ℝ)^2119 ≤ (32911529549643/100000000000000 : ℝ)^1607 := by
    have hnat : (2152474799 : ℕ)^2119*100000000000000^1607 ≤ 32911529549643^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152474799 5000000000 32911529549643 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997012887/10000000000 : ℝ)^2119 ≤ (8012126237579/20000000000000 : ℝ)^1607 := by
    have hnat : (4997012887 : ℕ)^2119*20000000000000^1607 ≤ 8012126237579^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997012887 10000000000 8012126237579 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707652391/10000000000 : ℝ)^2119 ≤ (27027839249143/100000000000000 : ℝ)^1607 := by
    have hnat : (3707652391 : ℕ)^2119*100000000000000^1607 ≤ 27027839249143^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707652391 10000000000 27027839249143 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152474799/5000000000 : ℝ), (4997012887/10000000000 : ℝ), (3707652391/10000000000 : ℝ)] ![(32911529549643/100000000000000 : ℝ), (8012126237579/20000000000000 : ℝ), (27027839249143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152474799/5000000000 : ℝ)|^2119 ≤ (32911529549643/100000000000000 : ℝ)^1607
        have hw : |(2152474799/5000000000 : ℝ)|=(2152474799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997012887/10000000000 : ℝ)|^2119 ≤ (8012126237579/20000000000000 : ℝ)^1607
        have hw : |(4997012887/10000000000 : ℝ)|=(4997012887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707652391/10000000000 : ℝ)|^2119 ≤ (27027839249143/100000000000000 : ℝ)^1607
        have hw : |(3707652391/10000000000 : ℝ)|=(3707652391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1567/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4991/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (923/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (380736590481/100000000000000000000 : ℝ) := by
    have hpowers : (923/100000 : ℝ)^4237 ≤ (380736590481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4237*100000000000000000000^1024 ≤ 380736590481^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 100000 380736590481 100000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/100000 : ℝ)) (X := (380736590481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27339/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (9345619674533921/2000000000000000000 : ℝ) := by
    have hpowers : (27339/100000 : ℝ)^4237 ≤ (9345619674533921/2000000000000000000 : ℝ)^1024 := by
      have hnat : (27339 : ℕ)^4237*2000000000000000000^1024 ≤ 9345619674533921^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27339 100000 9345619674533921 2000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27339/100000 : ℝ)) (X := (9345619674533921/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000380736590481/50000000000000000000 : ℝ) ≤ (10000000018403317/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50000000380736590481/50000000000000000000 : ℝ)^1024 ≤ (10000000018403317/10000000000000000 : ℝ)^4237 := by
      have hnat : (50000000380736590481 : ℕ)^1024*10000000000000000^4237 ≤ 10000000018403317^4237*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000380736590481 50000000000000000000 10000000018403317 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000018403317/10000000000000000 : ℝ)) (X := (50000000380736590481/50000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100467281364463286531/100000000000000000000 : ℝ) ≤ (156426145658579/156250000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (100467281364463286531/100000000000000000000 : ℝ)^1024 ≤ (156426145658579/156250000000000 : ℝ)^4237 := by
      have hnat : (100467281364463286531 : ℕ)^1024*156250000000000^4237 ≤ 156426145658579^4237*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100467281364463286531 100000000000000000000 156426145658579 156250000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156426145658579/156250000000000 : ℝ)) (X := (100467281364463286531/100000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1009345619674533921/1000000000000000000 : ℝ) ≤ (2004509325178959/2000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (1009345619674533921/1000000000000000000 : ℝ)^1024 ≤ (2004509325178959/2000000000000000 : ℝ)^4237 := by
      have hnat : (1009345619674533921 : ℕ)^1024*2000000000000000^4237 ≤ 2004509325178959^4237*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009345619674533921 1000000000000000000 2004509325178959 2000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004509325178959/2000000000000000 : ℝ)) (X := (1009345619674533921/1000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(380736590481/100000000000000000000 : ℝ) ≤ ((10159199614131822603/10160000000000000000 : ℝ)+2*(11273303745739/2641600000000000 : ℝ)*(923/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (10159199614131822603/10160000000000000000 : ℝ)+2*(11273303745739/2641600000000000 : ℝ)*(923/100000 : ℝ)=(10000000018403317/10000000000000000 : ℝ) by norm_num, show 1+2*(380736590481/100000000000000000000 : ℝ)=(50000000380736590481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9345619674533921/2000000000000000000 : ℝ)+(380736590481/100000000000000000000 : ℝ) ≤ ((10159199614131822603/10160000000000000000 : ℝ)+(11273303745739/2641600000000000 : ℝ)*((27339/100000 : ℝ)+(923/100000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (10159199614131822603/10160000000000000000 : ℝ)+(11273303745739/2641600000000000 : ℝ)*((27339/100000 : ℝ)+(923/100000 : ℝ))=(156426145658579/156250000000000 : ℝ) by norm_num, show 1+(9345619674533921/2000000000000000000 : ℝ)+(380736590481/100000000000000000000 : ℝ)=(100467281364463286531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9345619674533921/2000000000000000000 : ℝ) ≤ ((10159199614131822603/10160000000000000000 : ℝ)+2*(11273303745739/2641600000000000 : ℝ)*(27339/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (10159199614131822603/10160000000000000000 : ℝ)+2*(11273303745739/2641600000000000 : ℝ)*(27339/100000 : ℝ)=(2004509325178959/2000000000000000 : ℝ) by norm_num, show 1+2*(9345619674533921/2000000000000000000 : ℝ)=(1009345619674533921/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10159199614131822603/10160000000000000000 : ℝ)*(X 1 0+X 2 0)+(11273303745739/2641600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (923/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (10159199614131822603/10160000000000000000 : ℝ)) (alpha := (11273303745739/2641600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10159199614131822603/10160000000000000000 : ℝ)*(X 0 1+X 2 1)+(11273303745739/2641600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (923/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (10159199614131822603/10160000000000000000 : ℝ)) (alpha := (11273303745739/2641600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10159199614131822603/10160000000000000000 : ℝ)*(X 0 2+X 1 2)+(11273303745739/2641600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (923/100000 : ℝ)) (hi := (27339/100000 : ℝ)) (c := (10159199614131822603/10160000000000000000 : ℝ)) (alpha := (11273303745739/2641600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10208319/50000000 : ℝ)*X 0 0+(1418019511/2500000000 : ℝ)*X 0 1+(5024112623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412478427/10000000000 : ℝ)*X 1 0+(-298676459/1250000000 : ℝ)*X 1 1+(1004822493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706239119/5000000000 : ℝ)*X 2 0+(2512056313/5000000000 : ℝ)*X 2 1+(-2389411713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53794801/125000000 : ℝ)*X 0 0+(737972979/2000000000 : ℝ)*X 0 1+(78351047/156250000 : ℝ)*X 0 2+(53794801/125000000 : ℝ)*X 1 0+(737972979/2000000000 : ℝ)*X 1 1+(78351047/156250000 : ℝ)*X 1 2+(53794801/125000000 : ℝ)*X 2 0+(737972979/2000000000 : ℝ)*X 2 1+(78351047/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51058299/250000000 : ℝ)*X 0 0+(5032650847/10000000000 : ℝ)*X 0 1+(1132675329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245278097/10000000000 : ℝ)*X 1 0+(-1750147441/10000000000 : ℝ)*X 1 1+(566337701/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245278011/10000000000 : ℝ)*X 2 0+(5663376733/10000000000 : ℝ)*X 2 1+(-875073983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152474799/5000000000 : ℝ)*X 0 0+(4997012887/10000000000 : ℝ)*X 0 1+(3707652391/10000000000 : ℝ)*X 0 2+(2152474799/5000000000 : ℝ)*X 1 0+(4997012887/10000000000 : ℝ)*X 1 1+(3707652391/10000000000 : ℝ)*X 1 2+(2152474799/5000000000 : ℝ)*X 2 0+(4997012887/10000000000 : ℝ)*X 2 1+(3707652391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111555567780701867145847611/26000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4847987/10000000000000 : ℝ)*(base1) + (445233521/50000000000000 : ℝ)*(base19) + (836576049/100000000000000 : ℝ)*(base23) + (20910369/20000000000000 : ℝ)*(upper3) + (37706401/50000000000000 : ℝ)*(upper5) + (574562494182253/50000000000000 : ℝ)*(major0) + (574562494182253/50000000000000 : ℝ)*(major1) + (574562494182253/50000000000000 : ℝ)*(major2) + (1543297062662181/100000000000000 : ℝ)*(sp0) + (1543300656952453/100000000000000 : ℝ)*(sp1) + (771650355421723/50000000000000 : ℝ)*(sp2) + (2359205914297/312500000000 : ℝ)*(sp3) + (70831831/1562500000000 : ℝ)*(sp4) + (2345234639/100000000000000 : ℝ)*(sp7) + (754948286289549/100000000000000 : ℝ)*(f.failure) + (308660309483899/20000000000000 : ℝ)*(f.sum) + (26269496362687/66040000000000000000000000000 : ℝ)*base65 + (56759258032187589267/6604000000000000000000000000000000 : ℝ)*base67 + (2708369593159589267/6604000000000000000000000000000000 : ℝ)*base69 + (62827955305995589267/6604000000000000000000000000000000 : ℝ)*base71 + (210122063200887/66040000000000000000000000000 : ℝ)*base73 + (13462004867151589267/6604000000000000000000000000000000 : ℝ)*base75 + (45177466186927589267/6604000000000000000000000000000000 : ℝ)*base77 + (60660898696251589267/6604000000000000000000000000000000 : ℝ)*base79 + (105759605882873/66040000000000000000000000000 : ℝ)*base82 + (102607361/10000000000000000000000 : ℝ)*base90 + (102607361/10000000000000000000000 : ℝ)*base92 + (102607361/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1216865400238814551473255573/206375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20910737/100000000000000 : ℝ)*(base1) + (1104021049/100000000000000 : ℝ)*(base19) + (104268999/10000000000000 : ℝ)*(base23) + (1242191/781250000000 : ℝ)*(upper3) + (127682299/100000000000000 : ℝ)*(upper5) + (73782908307769/6250000000000 : ℝ)*(major0) + (73782908307769/6250000000000 : ℝ)*(major1) + (73782908307769/6250000000000 : ℝ)*(major2) + (2861093597/50000000000000 : ℝ)*(sp1) + (4613653103/100000000000000 : ℝ)*(sp2) + (1585474522346673/100000000000000 : ℝ)*(sp4) + (792733837613847/50000000000000 : ℝ)*(sp5) + (396367211273211/25000000000000 : ℝ)*(sp6) + (775578346955931/100000000000000 : ℝ)*(sp7) + (193894591966667/25000000000000 : ℝ)*(f.failure) + (49546078169873/3125000000000 : ℝ)*(f.sum) + (1546961065499/8255000000000000000000000000 : ℝ)*base66 + (5137209564548314809/825500000000000000000000000000000 : ℝ)*base68 + (1113997921962685191/825500000000000000000000000000000 : ℝ)*base69 + (6249061535531314809/825500000000000000000000000000000 : ℝ)*base72 + (3887789557167/4127500000000000000000000000 : ℝ)*base74 + (6061277849694814809/825500000000000000000000000000000 : ℝ)*base76 + (7857666862002314809/825500000000000000000000000000000 : ℝ)*base78 + (10420157868772814809/825500000000000000000000000000000 : ℝ)*base80 + (32344489401401/8255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15704137/2500000000000000000000 : ℝ)*base89 + (15704137/2500000000000000000000 : ℝ)*base91 + (15704137/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1278_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1567/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4991/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_s2_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-104384907/500000000 : ℝ)*x 0 + (219944991/400000000 : ℝ)*x 1 + (1292046571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104384907/500000000 : ℝ)^2119 ≤ (633694138921/5000000000000 : ℝ)^1607 := by
    have hnat : (104384907 : ℕ)^2119*5000000000000^1607 ≤ 633694138921^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104384907 500000000 633694138921 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219944991/400000000 : ℝ)^2119 ≤ (45446187071869/100000000000000 : ℝ)^1607 := by
    have hnat : (219944991 : ℕ)^2119*100000000000000^1607 ≤ 45446187071869^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219944991 400000000 45446187071869 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292046571/2500000000 : ℝ)^2119 ≤ (163593477081/390625000000 : ℝ)^1607 := by
    have hnat : (1292046571 : ℕ)^2119*390625000000^1607 ≤ 163593477081^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292046571 2500000000 163593477081 390625000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104384907/500000000 : ℝ), (219944991/400000000 : ℝ), (1292046571/2500000000 : ℝ)] ![(633694138921/5000000000000 : ℝ), (45446187071869/100000000000000 : ℝ), (163593477081/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104384907/500000000 : ℝ)|^2119 ≤ (633694138921/5000000000000 : ℝ)^1607
        have hw : |(-104384907/500000000 : ℝ)|=(104384907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219944991/400000000 : ℝ)|^2119 ≤ (45446187071869/100000000000000 : ℝ)^1607
        have hw : |(219944991/400000000 : ℝ)|=(219944991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292046571/2500000000 : ℝ)|^2119 ≤ (163593477081/390625000000 : ℝ)^1607
        have hw : |(1292046571/2500000000 : ℝ)|=(1292046571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335665107/625000000 : ℝ)*x 0 + (-451817749/2000000000 : ℝ)*x 1 + (5168187223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335665107/625000000 : ℝ)^2119 ≤ (5507073696187/12500000000000 : ℝ)^1607 := by
    have hnat : (335665107 : ℕ)^2119*12500000000000^1607 ≤ 5507073696187^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335665107 625000000 5507073696187 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451817749/2000000000 : ℝ)^2119 ≤ (703173512403/5000000000000 : ℝ)^1607 := by
    have hnat : (451817749 : ℕ)^2119*5000000000000^1607 ≤ 703173512403^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451817749 2000000000 703173512403 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168187223/10000000000 : ℝ)^2119 ≤ (81796758137/195312500000 : ℝ)^1607 := by
    have hnat : (5168187223 : ℕ)^2119*195312500000^1607 ≤ 81796758137^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168187223 10000000000 81796758137 195312500000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335665107/625000000 : ℝ), (-451817749/2000000000 : ℝ), (5168187223/10000000000 : ℝ)] ![(5507073696187/12500000000000 : ℝ), (703173512403/5000000000000 : ℝ), (81796758137/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335665107/625000000 : ℝ)|^2119 ≤ (5507073696187/12500000000000 : ℝ)^1607
        have hw : |(335665107/625000000 : ℝ)|=(335665107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451817749/2000000000 : ℝ)|^2119 ≤ (703173512403/5000000000000 : ℝ)^1607
        have hw : |(-451817749/2000000000 : ℝ)|=(451817749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168187223/10000000000 : ℝ)|^2119 ≤ (81796758137/195312500000 : ℝ)^1607
        have hw : |(5168187223/10000000000 : ℝ)|=(5168187223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268532113/500000000 : ℝ)*x 0 + (5168186459/10000000000 : ℝ)*x 1 + (-1129544509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268532113/500000000 : ℝ)^2119 ≤ (11014148874279/25000000000000 : ℝ)^1607 := by
    have hnat : (268532113 : ℕ)^2119*25000000000000^1607 ≤ 11014148874279^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268532113 500000000 11014148874279 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5168186459/10000000000 : ℝ)^2119 ≤ (41879932002647/100000000000000 : ℝ)^1607 := by
    have hnat : (5168186459 : ℕ)^2119*100000000000000^1607 ≤ 41879932002647^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168186459 10000000000 41879932002647 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129544509/5000000000 : ℝ)^2119 ≤ (2812694497807/20000000000000 : ℝ)^1607 := by
    have hnat : (1129544509 : ℕ)^2119*20000000000000^1607 ≤ 2812694497807^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129544509 5000000000 2812694497807 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268532113/500000000 : ℝ), (5168186459/10000000000 : ℝ), (-1129544509/5000000000 : ℝ)] ![(11014148874279/25000000000000 : ℝ), (41879932002647/100000000000000 : ℝ), (2812694497807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268532113/500000000 : ℝ)|^2119 ≤ (11014148874279/25000000000000 : ℝ)^1607
        have hw : |(268532113/500000000 : ℝ)|=(268532113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5168186459/10000000000 : ℝ)|^2119 ≤ (41879932002647/100000000000000 : ℝ)^1607
        have hw : |(5168186459/10000000000 : ℝ)|=(5168186459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129544509/5000000000 : ℝ)|^2119 ≤ (2812694497807/20000000000000 : ℝ)^1607
        have hw : |(-1129544509/5000000000 : ℝ)|=(1129544509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335527483/10000000000 : ℝ)*x 0 + (401039083/1000000000 : ℝ)*x 1 + (14643421/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335527483/10000000000 : ℝ)^2119 ≤ (8305031844427/25000000000000 : ℝ)^1607 := by
    have hnat : (4335527483 : ℕ)^2119*25000000000000^1607 ≤ 8305031844427^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335527483 10000000000 8305031844427 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401039083/1000000000 : ℝ)^2119 ≤ (749375636819/2500000000000 : ℝ)^1607 := by
    have hnat : (401039083 : ℕ)^2119*2500000000000^1607 ≤ 749375636819^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401039083 1000000000 749375636819 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14643421/31250000 : ℝ)^2119 ≤ (18402423570467/50000000000000 : ℝ)^1607 := by
    have hnat : (14643421 : ℕ)^2119*50000000000000^1607 ≤ 18402423570467^1607*31250000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14643421 31250000 18402423570467 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335527483/10000000000 : ℝ), (401039083/1000000000 : ℝ), (14643421/31250000 : ℝ)] ![(8305031844427/25000000000000 : ℝ), (749375636819/2500000000000 : ℝ), (18402423570467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335527483/10000000000 : ℝ)|^2119 ≤ (8305031844427/25000000000000 : ℝ)^1607
        have hw : |(4335527483/10000000000 : ℝ)|=(4335527483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401039083/1000000000 : ℝ)|^2119 ≤ (749375636819/2500000000000 : ℝ)^1607
        have hw : |(401039083/1000000000 : ℝ)|=(401039083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14643421/31250000 : ℝ)|^2119 ≤ (18402423570467/50000000000000 : ℝ)^1607
        have hw : |(14643421/31250000 : ℝ)|=(14643421/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087785811/10000000000 : ℝ)*x 0 + (258520829/500000000 : ℝ)*x 1 + (2748186697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087785811/10000000000 : ℝ)^2119 ≤ (12674584582563/100000000000000 : ℝ)^1607 := by
    have hnat : (2087785811 : ℕ)^2119*100000000000000^1607 ≤ 12674584582563^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087785811 10000000000 12674584582563 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258520829/500000000 : ℝ)^2119 ≤ (41903762941429/100000000000000 : ℝ)^1607 := by
    have hnat : (258520829 : ℕ)^2119*100000000000000^1607 ≤ 41903762941429^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258520829 500000000 41903762941429 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748186697/5000000000 : ℝ)^2119 ≤ (45421652464451/100000000000000 : ℝ)^1607 := by
    have hnat : (2748186697 : ℕ)^2119*100000000000000^1607 ≤ 45421652464451^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748186697 5000000000 45421652464451 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087785811/10000000000 : ℝ), (258520829/500000000 : ℝ), (2748186697/5000000000 : ℝ)] ![(12674584582563/100000000000000 : ℝ), (41903762941429/100000000000000 : ℝ), (45421652464451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087785811/10000000000 : ℝ)|^2119 ≤ (12674584582563/100000000000000 : ℝ)^1607
        have hw : |(-2087785811/10000000000 : ℝ)|=(2087785811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258520829/500000000 : ℝ)|^2119 ≤ (41903762941429/100000000000000 : ℝ)^1607
        have hw : |(258520829/500000000 : ℝ)|=(258520829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748186697/5000000000 : ℝ)|^2119 ≤ (45421652464451/100000000000000 : ℝ)^1607
        have hw : |(2748186697/5000000000 : ℝ)|=(2748186697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643045579/5000000000 : ℝ)*x 0 + (-1930901883/10000000000 : ℝ)*x 1 + (1099274711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643045579/5000000000 : ℝ)^2119 ≤ (43144323008523/100000000000000 : ℝ)^1607 := by
    have hnat : (2643045579 : ℕ)^2119*100000000000000^1607 ≤ 43144323008523^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643045579 5000000000 43144323008523 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930901883/10000000000 : ℝ)^2119 ≤ (714626421993/6250000000000 : ℝ)^1607 := by
    have hnat : (1930901883 : ℕ)^2119*6250000000000^1607 ≤ 714626421993^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930901883 10000000000 714626421993 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099274711/2000000000 : ℝ)^2119 ≤ (45421654218847/100000000000000 : ℝ)^1607 := by
    have hnat : (1099274711 : ℕ)^2119*100000000000000^1607 ≤ 45421654218847^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099274711 2000000000 45421654218847 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643045579/5000000000 : ℝ), (-1930901883/10000000000 : ℝ), (1099274711/2000000000 : ℝ)] ![(43144323008523/100000000000000 : ℝ), (714626421993/6250000000000 : ℝ), (45421654218847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643045579/5000000000 : ℝ)|^2119 ≤ (43144323008523/100000000000000 : ℝ)^1607
        have hw : |(2643045579/5000000000 : ℝ)|=(2643045579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930901883/10000000000 : ℝ)|^2119 ≤ (714626421993/6250000000000 : ℝ)^1607
        have hw : |(-1930901883/10000000000 : ℝ)|=(1930901883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099274711/2000000000 : ℝ)|^2119 ≤ (45421654218847/100000000000000 : ℝ)^1607
        have hw : |(1099274711/2000000000 : ℝ)|=(1099274711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286091347/10000000000 : ℝ)*x 0 + (1374093351/2500000000 : ℝ)*x 1 + (-965450917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286091347/10000000000 : ℝ)^2119 ≤ (43144325042593/100000000000000 : ℝ)^1607 := by
    have hnat : (5286091347 : ℕ)^2119*100000000000000^1607 ≤ 43144325042593^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286091347 10000000000 43144325042593 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374093351/2500000000 : ℝ)^2119 ≤ (2271082628671/5000000000000 : ℝ)^1607 := by
    have hnat : (1374093351 : ℕ)^2119*5000000000000^1607 ≤ 2271082628671^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374093351 2500000000 2271082628671 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965450917/5000000000 : ℝ)^2119 ≤ (2858505592321/25000000000000 : ℝ)^1607 := by
    have hnat : (965450917 : ℕ)^2119*25000000000000^1607 ≤ 2858505592321^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965450917 5000000000 2858505592321 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286091347/10000000000 : ℝ), (1374093351/2500000000 : ℝ), (-965450917/5000000000 : ℝ)] ![(43144325042593/100000000000000 : ℝ), (2271082628671/5000000000000 : ℝ), (2858505592321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286091347/10000000000 : ℝ)|^2119 ≤ (43144325042593/100000000000000 : ℝ)^1607
        have hw : |(5286091347/10000000000 : ℝ)|=(5286091347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374093351/2500000000 : ℝ)|^2119 ≤ (2271082628671/5000000000000 : ℝ)^1607
        have hw : |(1374093351/2500000000 : ℝ)|=(1374093351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965450917/5000000000 : ℝ)|^2119 ≤ (2858505592321/25000000000000 : ℝ)^1607
        have hw : |(-965450917/5000000000 : ℝ)|=(965450917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s2_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (541963389/1250000000 : ℝ)*x 0 + (4681334621/10000000000 : ℝ)*x 1 + (501874633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541963389/1250000000 : ℝ)^2119 ≤ (16610971141043/50000000000000 : ℝ)^1607 := by
    have hnat : (541963389 : ℕ)^2119*50000000000000^1607 ≤ 16610971141043^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541963389 1250000000 16610971141043 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4681334621/10000000000 : ℝ)^2119 ≤ (36757626215351/100000000000000 : ℝ)^1607 := by
    have hnat : (4681334621 : ℕ)^2119*100000000000000^1607 ≤ 36757626215351^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4681334621 10000000000 36757626215351 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501874633/1250000000 : ℝ)^2119 ≤ (7505107871577/25000000000000 : ℝ)^1607 := by
    have hnat : (501874633 : ℕ)^2119*25000000000000^1607 ≤ 7505107871577^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501874633 1250000000 7505107871577 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541963389/1250000000 : ℝ), (4681334621/10000000000 : ℝ), (501874633/1250000000 : ℝ)] ![(16610971141043/50000000000000 : ℝ), (36757626215351/100000000000000 : ℝ), (7505107871577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541963389/1250000000 : ℝ)|^2119 ≤ (16610971141043/50000000000000 : ℝ)^1607
        have hw : |(541963389/1250000000 : ℝ)|=(541963389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4681334621/10000000000 : ℝ)|^2119 ≤ (36757626215351/100000000000000 : ℝ)^1607
        have hw : |(4681334621/10000000000 : ℝ)|=(4681334621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501874633/1250000000 : ℝ)|^2119 ≤ (7505107871577/25000000000000 : ℝ)^1607
        have hw : |(501874633/1250000000 : ℝ)|=(501874633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4991/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1567/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (47/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16383/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4991/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1567/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4991/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1567/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4991/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1567/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4991/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1567/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4991/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1567/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4991/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1567/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1567/25000 : ℝ) ^ (4237/1024 : ℝ) ≤ (210822154320551/20000000000000000000 : ℝ) := by
    have hpowers : (1567/25000 : ℝ)^4237 ≤ (210822154320551/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1567 : ℕ)^4237*20000000000000000000^1024 ≤ 210822154320551^1024*25000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1567 25000 210822154320551 20000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1567/25000 : ℝ)) (X := (210822154320551/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4991/25000 : ℝ) ^ (4237/1024 : ℝ) ≤ (25448817641278249/20000000000000000000 : ℝ) := by
    have hpowers : (4991/25000 : ℝ)^4237 ≤ (25448817641278249/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4991 : ℕ)^4237*20000000000000000000^1024 ≤ 25448817641278249^1024*25000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4991 25000 25448817641278249 20000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4991/25000 : ℝ)) (X := (25448817641278249/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000210822154320551/10000000000000000000 : ℝ) ≤ (2500012737795633/2500000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (10000210822154320551/10000000000000000000 : ℝ)^1024 ≤ (2500012737795633/2500000000000000 : ℝ)^4237 := by
      have hnat : (10000210822154320551 : ℕ)^1024*2500000000000000^4237 ≤ 2500012737795633^4237*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000210822154320551 10000000000000000000 2500012737795633 2500000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012737795633/2500000000000000 : ℝ)) (X := (10000210822154320551/10000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50064149099488997/50000000000000000 : ℝ) ≤ (10003099209218177/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50064149099488997/50000000000000000 : ℝ)^1024 ≤ (10003099209218177/10000000000000000 : ℝ)^4237 := by
      have hnat : (50064149099488997 : ℕ)^1024*10000000000000000^4237 ≤ 10003099209218177^4237*50000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064149099488997 50000000000000000 10003099209218177 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003099209218177/10000000000000000 : ℝ)) (X := (50064149099488997/50000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10025448817641278249/10000000000000000000 : ℝ) ≤ (5003073733626911/5000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (10025448817641278249/10000000000000000000 : ℝ)^1024 ≤ (5003073733626911/5000000000000000 : ℝ)^4237 := by
      have hnat : (10025448817641278249 : ℕ)^1024*5000000000000000^4237 ≤ 5003073733626911^4237*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10025448817641278249 10000000000000000000 5003073733626911 5000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003073733626911/5000000000000000 : ℝ)) (X := (10025448817641278249/10000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(210822154320551/20000000000000000000 : ℝ) ≤ ((17115310608082639069/17120000000000000000 : ℝ)+2*(609651607129/273920000000000 : ℝ)*(1567/25000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (17115310608082639069/17120000000000000000 : ℝ)+2*(609651607129/273920000000000 : ℝ)*(1567/25000 : ℝ)=(2500012737795633/2500000000000000 : ℝ) by norm_num, show 1+2*(210822154320551/20000000000000000000 : ℝ)=(10000210822154320551/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25448817641278249/20000000000000000000 : ℝ)+(210822154320551/20000000000000000000 : ℝ) ≤ ((17115310608082639069/17120000000000000000 : ℝ)+(609651607129/273920000000000 : ℝ)*((4991/25000 : ℝ)+(1567/25000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (17115310608082639069/17120000000000000000 : ℝ)+(609651607129/273920000000000 : ℝ)*((4991/25000 : ℝ)+(1567/25000 : ℝ))=(10003099209218177/10000000000000000 : ℝ) by norm_num, show 1+(25448817641278249/20000000000000000000 : ℝ)+(210822154320551/20000000000000000000 : ℝ)=(50064149099488997/50000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25448817641278249/20000000000000000000 : ℝ) ≤ ((17115310608082639069/17120000000000000000 : ℝ)+2*(609651607129/273920000000000 : ℝ)*(4991/25000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (17115310608082639069/17120000000000000000 : ℝ)+2*(609651607129/273920000000000 : ℝ)*(4991/25000 : ℝ)=(5003073733626911/5000000000000000 : ℝ) by norm_num, show 1+2*(25448817641278249/20000000000000000000 : ℝ)=(10025448817641278249/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17115310608082639069/17120000000000000000 : ℝ)*(X 1 0+X 2 0)+(609651607129/273920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (1567/25000 : ℝ)) (hi := (4991/25000 : ℝ)) (c := (17115310608082639069/17120000000000000000 : ℝ)) (alpha := (609651607129/273920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17115310608082639069/17120000000000000000 : ℝ)*(X 0 1+X 2 1)+(609651607129/273920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (1567/25000 : ℝ)) (hi := (4991/25000 : ℝ)) (c := (17115310608082639069/17120000000000000000 : ℝ)) (alpha := (609651607129/273920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17115310608082639069/17120000000000000000 : ℝ)*(X 0 2+X 1 2)+(609651607129/273920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (1567/25000 : ℝ)) (hi := (4991/25000 : ℝ)) (c := (17115310608082639069/17120000000000000000 : ℝ)) (alpha := (609651607129/273920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104384907/500000000 : ℝ)*X 0 0+(219944991/400000000 : ℝ)*X 0 1+(1292046571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335665107/625000000 : ℝ)*X 1 0+(-451817749/2000000000 : ℝ)*X 1 1+(5168187223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268532113/500000000 : ℝ)*X 2 0+(5168186459/10000000000 : ℝ)*X 2 1+(-1129544509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335527483/10000000000 : ℝ)*X 0 0+(401039083/1000000000 : ℝ)*X 0 1+(14643421/31250000 : ℝ)*X 0 2+(4335527483/10000000000 : ℝ)*X 1 0+(401039083/1000000000 : ℝ)*X 1 1+(14643421/31250000 : ℝ)*X 1 2+(4335527483/10000000000 : ℝ)*X 2 0+(401039083/1000000000 : ℝ)*X 2 1+(14643421/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087785811/10000000000 : ℝ)*X 0 0+(258520829/500000000 : ℝ)*X 0 1+(2748186697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643045579/5000000000 : ℝ)*X 1 0+(-1930901883/10000000000 : ℝ)*X 1 1+(1099274711/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286091347/10000000000 : ℝ)*X 2 0+(1374093351/2500000000 : ℝ)*X 2 1+(-965450917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((541963389/1250000000 : ℝ)*X 0 0+(4681334621/10000000000 : ℝ)*X 0 1+(501874633/1250000000 : ℝ)*X 0 2+(541963389/1250000000 : ℝ)*X 1 0+(4681334621/10000000000 : ℝ)*X 1 1+(501874633/1250000000 : ℝ)*X 1 2+(541963389/1250000000 : ℝ)*X 2 0+(4681334621/10000000000 : ℝ)*X 2 1+(501874633/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71284085648909711064201/13696000000000000000000000000 : ℝ) := by norm_num
    linear_combination (918839199/50000000000000 : ℝ)*(base19) + (266993667/12500000000000 : ℝ)*(base23) + (2825963/50000000000000 : ℝ)*(lower2) + (57288623/12500000000000 : ℝ)*(upper3) + (330898117/100000000000000 : ℝ)*(upper5) + (2253368436310213/100000000000000 : ℝ)*(major0) + (2253368436310213/100000000000000 : ℝ)*(major1) + (2253368436310213/100000000000000 : ℝ)*(major2) + (75657612525741/2500000000000 : ℝ)*(sp0) + (378290551622751/12500000000000 : ℝ)*(sp1) + (302632411471107/10000000000000 : ℝ)*(sp2) + (370098114849637/25000000000000 : ℝ)*(sp3) + (10874815383/50000000000000 : ℝ)*(sp4) + (4497267553/25000000000000 : ℝ)*(sp7) + (37010261211719/2500000000000 : ℝ)*(f.failure) + (1513163125330203/50000000000000 : ℝ)*(f.sum) + (5992722121497/2739200000000000000000000000 : ℝ)*base65 + (4499577721586675803/1712000000000000000000000000000000 : ℝ)*base68 + (5593234223373324197/1712000000000000000000000000000000 : ℝ)*base69 + (16586434027789324197/1712000000000000000000000000000000 : ℝ)*base71 + (3337850256359/2739200000000000000000000000 : ℝ)*base74 + (8415695785266675803/1712000000000000000000000000000000 : ℝ)*base76 + (6973254835058675803/1712000000000000000000000000000000 : ℝ)*base78 + (9618310695213324197/1712000000000000000000000000000000 : ℝ)*base79 + (63445081396349/13696000000000000000000000000 : ℝ)*base81 + (2055491/250000000000000000000 : ℝ)*base90 + (2055491/250000000000000000000 : ℝ)*base92 + (2055491/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7538182116101896935217241793/856000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1650616041/100000000000000 : ℝ)*(base19) + (1001162027/50000000000000 : ℝ)*(base23) + (1249993/500000000000 : ℝ)*(upper3) + (22837743/25000000000000 : ℝ)*(lower4) + (4115041/3125000000000 : ℝ)*(upper5) + (2284315203536999/100000000000000 : ℝ)*(major0) + (2284315203536999/100000000000000 : ℝ)*(major1) + (2284315203536999/100000000000000 : ℝ)*(major2) + (4134619229/25000000000000 : ℝ)*(sp1) + (20865034937/100000000000000 : ℝ)*(sp2) + (766972090393583/25000000000000 : ℝ)*(sp4) + (1533935086240687/50000000000000 : ℝ)*(sp5) + (3067865494215341/100000000000000 : ℝ)*(sp6) + (187592718994593/12500000000000 : ℝ)*(sp7) + (187592718994593/12500000000000 : ℝ)*(f.failure) + (766972090393583/25000000000000 : ℝ)*(f.sum) + (2489429053401/547840000000000000000000000 : ℝ)*base66 + (1634755931586648569/1712000000000000000000000000000000 : ℝ)*base68 + (6019486774333351431/1712000000000000000000000000000000 : ℝ)*base69 + (6257354571522648569/1712000000000000000000000000000000 : ℝ)*base72 + (32829082291919/13696000000000000000000000000 : ℝ)*base73 + (10167344290973351431/1712000000000000000000000000000000 : ℝ)*base75 + (2154684666578648569/1712000000000000000000000000000000 : ℝ)*base78 + (6790074630930648569/1712000000000000000000000000000000 : ℝ)*base80 + (9963941991619/2739200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8993723/1250000000000000000000 : ℝ)*base89 + (8993723/1250000000000000000000 : ℝ)*base91 + (8993723/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1278_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4991/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1567/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1278_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1278_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1278_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1278_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
