-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:16:32.225218+00:00
-- url     : https://prove2.me/submissions/d1371c83-1af4-4586-bfe9-b8747d839340

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
theorem support_rectangle_w1235_s3_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-530071831/2500000000 : ℝ)*x 0 + (2710134911/5000000000 : ℝ)*x 1 + (524008111/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530071831/2500000000 : ℝ)^2107 ≤ (6443700016189/50000000000000 : ℝ)^1595 := by
    have hnat : (530071831 : ℕ)^2107*50000000000000^1595 ≤ 6443700016189^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530071831 2500000000 6443700016189 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710134911/5000000000 : ℝ)^2107 ≤ (44528778665749/100000000000000 : ℝ)^1595 := by
    have hnat : (2710134911 : ℕ)^2107*100000000000000^1595 ≤ 44528778665749^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710134911 5000000000 44528778665749 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524008111/1000000000 : ℝ)^2107 ≤ (42583821289167/100000000000000 : ℝ)^1595 := by
    have hnat : (524008111 : ℕ)^2107*100000000000000^1595 ≤ 42583821289167^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524008111 1000000000 42583821289167 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530071831/2500000000 : ℝ), (2710134911/5000000000 : ℝ), (524008111/1000000000 : ℝ)] ![(6443700016189/50000000000000 : ℝ), (44528778665749/100000000000000 : ℝ), (42583821289167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530071831/2500000000 : ℝ)|^2107 ≤ (6443700016189/50000000000000 : ℝ)^1595
        have hw : |(-530071831/2500000000 : ℝ)|=(530071831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710134911/5000000000 : ℝ)|^2107 ≤ (44528778665749/100000000000000 : ℝ)^1595
        have hw : |(2710134911/5000000000 : ℝ)|=(2710134911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524008111/1000000000 : ℝ)|^2107 ≤ (42583821289167/100000000000000 : ℝ)^1595
        have hw : |(524008111/1000000000 : ℝ)|=(524008111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53516433/100000000 : ℝ)*x 0 + (-553055081/2500000000 : ℝ)*x 1 + (5240081259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53516433/100000000 : ℝ)^2107 ≤ (21892768773401/50000000000000 : ℝ)^1595 := by
    have hnat : (53516433 : ℕ)^2107*50000000000000^1595 ≤ 21892768773401^1595*100000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53516433 100000000 21892768773401 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553055081/2500000000 : ℝ)^2107 ≤ (13630639550077/100000000000000 : ℝ)^1595 := by
    have hnat : (553055081 : ℕ)^2107*100000000000000^1595 ≤ 13630639550077^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553055081 2500000000 13630639550077 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240081259/10000000000 : ℝ)^2107 ≤ (42583822888713/100000000000000 : ℝ)^1595 := by
    have hnat : (5240081259 : ℕ)^2107*100000000000000^1595 ≤ 42583822888713^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240081259 10000000000 42583822888713 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53516433/100000000 : ℝ), (-553055081/2500000000 : ℝ), (5240081259/10000000000 : ℝ)] ![(21892768773401/50000000000000 : ℝ), (13630639550077/100000000000000 : ℝ), (42583822888713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53516433/100000000 : ℝ)|^2107 ≤ (21892768773401/50000000000000 : ℝ)^1595
        have hw : |(53516433/100000000 : ℝ)|=(53516433/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553055081/2500000000 : ℝ)|^2107 ≤ (13630639550077/100000000000000 : ℝ)^1595
        have hw : |(-553055081/2500000000 : ℝ)|=(553055081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240081259/10000000000 : ℝ)|^2107 ≤ (42583822888713/100000000000000 : ℝ)^1595
        have hw : |(5240081259/10000000000 : ℝ)|=(5240081259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (3344777/6250000 : ℝ)*x 0 + (1310020419/2500000000 : ℝ)*x 1 + (-553054977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3344777/6250000 : ℝ)^2107 ≤ (43785536465997/100000000000000 : ℝ)^1595 := by
    have hnat : (3344777 : ℕ)^2107*100000000000000^1595 ≤ 43785536465997^1595*6250000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3344777 6250000 43785536465997 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310020419/2500000000 : ℝ)^2107 ≤ (8516765473059/20000000000000 : ℝ)^1595 := by
    have hnat : (1310020419 : ℕ)^2107*20000000000000^1595 ≤ 8516765473059^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310020419 2500000000 8516765473059 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553054977/2500000000 : ℝ)^2107 ≤ (3407659041023/25000000000000 : ℝ)^1595 := by
    have hnat : (553054977 : ℕ)^2107*25000000000000^1595 ≤ 3407659041023^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553054977 2500000000 3407659041023 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3344777/6250000 : ℝ), (1310020419/2500000000 : ℝ), (-553054977/2500000000 : ℝ)] ![(43785536465997/100000000000000 : ℝ), (8516765473059/20000000000000 : ℝ), (3407659041023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3344777/6250000 : ℝ)|^2107 ≤ (43785536465997/100000000000000 : ℝ)^1595
        have hw : |(3344777/6250000 : ℝ)|=(3344777/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310020419/2500000000 : ℝ)|^2107 ≤ (8516765473059/20000000000000 : ℝ)^1595
        have hw : |(1310020419/2500000000 : ℝ)|=(1310020419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553054977/2500000000 : ℝ)|^2107 ≤ (3407659041023/25000000000000 : ℝ)^1595
        have hw : |(-553054977/2500000000 : ℝ)|=(553054977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4350001641/10000000000 : ℝ)*x 0 + (260700711/625000000 : ℝ)*x 1 + (283515101/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350001641/10000000000 : ℝ)^2107 ≤ (33299935445949/100000000000000 : ℝ)^1595 := by
    have hnat : (4350001641 : ℕ)^2107*100000000000000^1595 ≤ 33299935445949^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350001641 10000000000 33299935445949 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260700711/625000000 : ℝ)^2107 ≤ (15751980947561/50000000000000 : ℝ)^1595 := by
    have hnat : (260700711 : ℕ)^2107*50000000000000^1595 ≤ 15751980947561^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260700711 625000000 15751980947561 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283515101/625000000 : ℝ)^2107 ≤ (1407844106001/4000000000000 : ℝ)^1595 := by
    have hnat : (283515101 : ℕ)^2107*4000000000000^1595 ≤ 1407844106001^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283515101 625000000 1407844106001 4000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350001641/10000000000 : ℝ), (260700711/625000000 : ℝ), (283515101/625000000 : ℝ)] ![(33299935445949/100000000000000 : ℝ), (15751980947561/50000000000000 : ℝ), (1407844106001/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350001641/10000000000 : ℝ)|^2107 ≤ (33299935445949/100000000000000 : ℝ)^1595
        have hw : |(4350001641/10000000000 : ℝ)|=(4350001641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260700711/625000000 : ℝ)|^2107 ≤ (15751980947561/50000000000000 : ℝ)^1595
        have hw : |(260700711/625000000 : ℝ)|=(260700711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283515101/625000000 : ℝ)|^2107 ≤ (1407844106001/4000000000000 : ℝ)^1595
        have hw : |(283515101/625000000 : ℝ)|=(283515101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-106015087/500000000 : ℝ)*x 0 + (5240738971/10000000000 : ℝ)*x 1 + (541960837/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106015087/500000000 : ℝ)^2107 ≤ (12887515782029/100000000000000 : ℝ)^1595 := by
    have hnat : (106015087 : ℕ)^2107*100000000000000^1595 ≤ 12887515782029^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106015087 500000000 12887515782029 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240738971/10000000000 : ℝ)^2107 ≤ (21295441853117/50000000000000 : ℝ)^1595 := by
    have hnat : (5240738971 : ℕ)^2107*50000000000000^1595 ≤ 21295441853117^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240738971 10000000000 21295441853117 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541960837/1000000000 : ℝ)^2107 ≤ (44521600498837/100000000000000 : ℝ)^1595 := by
    have hnat : (541960837 : ℕ)^2107*100000000000000^1595 ≤ 44521600498837^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541960837 1000000000 44521600498837 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106015087/500000000 : ℝ), (5240738971/10000000000 : ℝ), (541960837/1000000000 : ℝ)] ![(12887515782029/100000000000000 : ℝ), (21295441853117/50000000000000 : ℝ), (44521600498837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106015087/500000000 : ℝ)|^2107 ≤ (12887515782029/100000000000000 : ℝ)^1595
        have hw : |(-106015087/500000000 : ℝ)|=(106015087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240738971/10000000000 : ℝ)|^2107 ≤ (21295441853117/50000000000000 : ℝ)^1595
        have hw : |(5240738971/10000000000 : ℝ)|=(5240738971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541960837/1000000000 : ℝ)|^2107 ≤ (44521600498837/100000000000000 : ℝ)^1595
        have hw : |(541960837/1000000000 : ℝ)|=(541960837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652847079/5000000000 : ℝ)*x 0 + (-406538679/2000000000 : ℝ)*x 1 + (338725533/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652847079/5000000000 : ℝ)^2107 ≤ (5411200324797/12500000000000 : ℝ)^1595 := by
    have hnat : (2652847079 : ℕ)^2107*12500000000000^1595 ≤ 5411200324797^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652847079 5000000000 5411200324797 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406538679/2000000000 : ℝ)^2107 ≤ (12188795176523/100000000000000 : ℝ)^1595 := by
    have hnat : (406538679 : ℕ)^2107*100000000000000^1595 ≤ 12188795176523^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406538679 2000000000 12188795176523 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338725533/625000000 : ℝ)^2107 ≤ (44521602213441/100000000000000 : ℝ)^1595 := by
    have hnat : (338725533 : ℕ)^2107*100000000000000^1595 ≤ 44521602213441^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338725533 625000000 44521602213441 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652847079/5000000000 : ℝ), (-406538679/2000000000 : ℝ), (338725533/625000000 : ℝ)] ![(5411200324797/12500000000000 : ℝ), (12188795176523/100000000000000 : ℝ), (44521602213441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652847079/5000000000 : ℝ)|^2107 ≤ (5411200324797/12500000000000 : ℝ)^1595
        have hw : |(2652847079/5000000000 : ℝ)|=(2652847079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406538679/2000000000 : ℝ)|^2107 ≤ (12188795176523/100000000000000 : ℝ)^1595
        have hw : |(-406538679/2000000000 : ℝ)|=(406538679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338725533/625000000 : ℝ)|^2107 ≤ (44521602213441/100000000000000 : ℝ)^1595
        have hw : |(338725533/625000000 : ℝ)|=(338725533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694401/10000000000 : ℝ)*x 0 + (1083921679/2000000000 : ℝ)*x 1 + (-1016346623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694401/10000000000 : ℝ)^2107 ≤ (676400081523/1562500000000 : ℝ)^1595 := by
    have hnat : (5305694401 : ℕ)^2107*1562500000000^1595 ≤ 676400081523^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694401 10000000000 676400081523 1562500000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083921679/2000000000 : ℝ)^2107 ≤ (8904320154027/20000000000000 : ℝ)^1595 := by
    have hnat : (1083921679 : ℕ)^2107*20000000000000^1595 ≤ 8904320154027^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083921679 2000000000 8904320154027 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016346623/5000000000 : ℝ)^2107 ≤ (12188793996259/100000000000000 : ℝ)^1595 := by
    have hnat : (1016346623 : ℕ)^2107*100000000000000^1595 ≤ 12188793996259^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016346623 5000000000 12188793996259 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694401/10000000000 : ℝ), (1083921679/2000000000 : ℝ), (-1016346623/5000000000 : ℝ)] ![(676400081523/1562500000000 : ℝ), (8904320154027/20000000000000 : ℝ), (12188793996259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694401/10000000000 : ℝ)|^2107 ≤ (676400081523/1562500000000 : ℝ)^1595
        have hw : |(5305694401/10000000000 : ℝ)|=(5305694401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083921679/2000000000 : ℝ)|^2107 ≤ (8904320154027/20000000000000 : ℝ)^1595
        have hw : |(1083921679/2000000000 : ℝ)|=(1083921679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016346623/5000000000 : ℝ)|^2107 ≤ (12188793996259/100000000000000 : ℝ)^1595
        have hw : |(-1016346623/5000000000 : ℝ)|=(1016346623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s3_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2175015321/5000000000 : ℝ)*x 0 + (1133727367/2500000000 : ℝ)*x 1 + (4172550357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175015321/5000000000 : ℝ)^2107 ≤ (4162528589799/12500000000000 : ℝ)^1595 := by
    have hnat : (2175015321 : ℕ)^2107*12500000000000^1595 ≤ 4162528589799^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175015321 5000000000 4162528589799 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133727367/2500000000 : ℝ)^2107 ≤ (17591224728181/50000000000000 : ℝ)^1595 := by
    have hnat : (1133727367 : ℕ)^2107*50000000000000^1595 ≤ 17591224728181^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133727367 2500000000 17591224728181 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172550357/10000000000 : ℝ)^2107 ≤ (7879330451887/25000000000000 : ℝ)^1595 := by
    have hnat : (4172550357 : ℕ)^2107*25000000000000^1595 ≤ 7879330451887^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172550357 10000000000 7879330451887 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175015321/5000000000 : ℝ), (1133727367/2500000000 : ℝ), (4172550357/10000000000 : ℝ)] ![(4162528589799/12500000000000 : ℝ), (17591224728181/50000000000000 : ℝ), (7879330451887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175015321/5000000000 : ℝ)|^2107 ≤ (4162528589799/12500000000000 : ℝ)^1595
        have hw : |(2175015321/5000000000 : ℝ)|=(2175015321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133727367/2500000000 : ℝ)|^2107 ≤ (17591224728181/50000000000000 : ℝ)^1595
        have hw : |(1133727367/2500000000 : ℝ)|=(1133727367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172550357/10000000000 : ℝ)|^2107 ≤ (7879330451887/25000000000000 : ℝ)^1595
        have hw : |(4172550357/10000000000 : ℝ)|=(4172550357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9471/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (6139440109387849/100000000000000000000 : ℝ) := by
    have hpowers : (9471/100000 : ℝ)^8427 ≤ (6139440109387849/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9471 : ℕ)^8427*100000000000000000000^2048 ≤ 6139440109387849^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9471 100000 6139440109387849 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9471/100000 : ℝ)) (X := (6139440109387849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16241/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (7059630600195447/12500000000000000000 : ℝ) := by
    have hpowers : (16241/100000 : ℝ)^8427 ≤ (7059630600195447/12500000000000000000 : ℝ)^2048 := by
      have hnat : (16241 : ℕ)^8427*12500000000000000000^2048 ≤ 7059630600195447^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16241 100000 7059630600195447 12500000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16241/100000 : ℝ)) (X := (7059630600195447/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006139440109387849/50000000000000000000 : ℝ) ≤ (2500074599436597/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50006139440109387849/50000000000000000000 : ℝ)^2048 ≤ (2500074599436597/2500000000000000 : ℝ)^8427 := by
      have hnat : (50006139440109387849 : ℕ)^2048*2500000000000000^8427 ≤ 2500074599436597^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006139440109387849 50000000000000000000 2500074599436597 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074599436597/2500000000000000 : ℝ)) (X := (50006139440109387849/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002504659396438057/4000000000000000000 : ℝ) ≤ (625095087353449/625000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (4002504659396438057/4000000000000000000 : ℝ)^2048 ≤ (625095087353449/625000000000000 : ℝ)^8427 := by
      have hnat : (4002504659396438057 : ℕ)^2048*625000000000000^8427 ≤ 625095087353449^8427*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002504659396438057 4000000000000000000 625095087353449 625000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625095087353449/625000000000000 : ℝ)) (X := (4002504659396438057/4000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6257059630600195447/6250000000000000000 : ℝ) ≤ (500137219878199/500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (6257059630600195447/6250000000000000000 : ℝ)^2048 ≤ (500137219878199/500000000000000 : ℝ)^8427 := by
      have hnat : (6257059630600195447 : ℕ)^2048*500000000000000^8427 ≤ 500137219878199^8427*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257059630600195447 6250000000000000000 500137219878199 500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500137219878199/500000000000000 : ℝ)) (X := (6257059630600195447/6250000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6139440109387849/100000000000000000000 : ℝ) ≤ ((2114964190264707279/2115625000000000000 : ℝ)+2*(305749977199/169250000000000 : ℝ)*(9471/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (2114964190264707279/2115625000000000000 : ℝ)+2*(305749977199/169250000000000 : ℝ)*(9471/100000 : ℝ)=(2500074599436597/2500000000000000 : ℝ) by norm_num, show 1+2*(6139440109387849/100000000000000000000 : ℝ)=(50006139440109387849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7059630600195447/12500000000000000000 : ℝ)+(6139440109387849/100000000000000000000 : ℝ) ≤ ((2114964190264707279/2115625000000000000 : ℝ)+(305749977199/169250000000000 : ℝ)*((16241/100000 : ℝ)+(9471/100000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (2114964190264707279/2115625000000000000 : ℝ)+(305749977199/169250000000000 : ℝ)*((16241/100000 : ℝ)+(9471/100000 : ℝ))=(625095087353449/625000000000000 : ℝ) by norm_num, show 1+(7059630600195447/12500000000000000000 : ℝ)+(6139440109387849/100000000000000000000 : ℝ)=(4002504659396438057/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7059630600195447/12500000000000000000 : ℝ) ≤ ((2114964190264707279/2115625000000000000 : ℝ)+2*(305749977199/169250000000000 : ℝ)*(16241/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (2114964190264707279/2115625000000000000 : ℝ)+2*(305749977199/169250000000000 : ℝ)*(16241/100000 : ℝ)=(500137219878199/500000000000000 : ℝ) by norm_num, show 1+2*(7059630600195447/12500000000000000000 : ℝ)=(6257059630600195447/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2114964190264707279/2115625000000000000 : ℝ)*(X 1 0+X 2 0)+(305749977199/169250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (9471/100000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (2114964190264707279/2115625000000000000 : ℝ)) (alpha := (305749977199/169250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2114964190264707279/2115625000000000000 : ℝ)*(X 0 1+X 2 1)+(305749977199/169250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (9471/100000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (2114964190264707279/2115625000000000000 : ℝ)) (alpha := (305749977199/169250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2114964190264707279/2115625000000000000 : ℝ)*(X 0 2+X 1 2)+(305749977199/169250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (9471/100000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (2114964190264707279/2115625000000000000 : ℝ)) (alpha := (305749977199/169250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-530071831/2500000000 : ℝ)*X 0 0+(2710134911/5000000000 : ℝ)*X 0 1+(524008111/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53516433/100000000 : ℝ)*X 1 0+(-553055081/2500000000 : ℝ)*X 1 1+(5240081259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((3344777/6250000 : ℝ)*X 2 0+(1310020419/2500000000 : ℝ)*X 2 1+(-553054977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350001641/10000000000 : ℝ)*X 0 0+(260700711/625000000 : ℝ)*X 0 1+(283515101/625000000 : ℝ)*X 0 2+(4350001641/10000000000 : ℝ)*X 1 0+(260700711/625000000 : ℝ)*X 1 1+(283515101/625000000 : ℝ)*X 1 2+(4350001641/10000000000 : ℝ)*X 2 0+(260700711/625000000 : ℝ)*X 2 1+(283515101/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106015087/500000000 : ℝ)*X 0 0+(5240738971/10000000000 : ℝ)*X 0 1+(541960837/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652847079/5000000000 : ℝ)*X 1 0+(-406538679/2000000000 : ℝ)*X 1 1+(338725533/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305694401/10000000000 : ℝ)*X 2 0+(1083921679/2000000000 : ℝ)*X 2 1+(-1016346623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175015321/5000000000 : ℝ)*X 0 0+(1133727367/2500000000 : ℝ)*X 0 1+(4172550357/10000000000 : ℝ)*X 0 2+(2175015321/5000000000 : ℝ)*X 1 0+(1133727367/2500000000 : ℝ)*X 1 1+(4172550357/10000000000 : ℝ)*X 1 2+(2175015321/5000000000 : ℝ)*X 2 0+(1133727367/2500000000 : ℝ)*X 2 1+(4172550357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24148642232967636983364027/2644531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (676980987/50000000000000 : ℝ)*(base19) + (916785243/100000000000000 : ℝ)*(base23) + (182784451/100000000000000 : ℝ)*(lower2) + (42096597/25000000000000 : ℝ)*(upper5) + (207233425262129/5000000000000 : ℝ)*(major0) + (207233425262129/5000000000000 : ℝ)*(major1) + (207233425262129/5000000000000 : ℝ)*(major2) + (5549769365613181/100000000000000 : ℝ)*(sp0) + (1387452129050189/25000000000000 : ℝ)*(sp1) + (221992395751959/4000000000000 : ℝ)*(sp2) + (34243914150421/1250000000000 : ℝ)*(sp3) + (41444971037/100000000000000 : ℝ)*(sp4) + (940421487/100000000000000 : ℝ)*(sp5) + (6381741299/50000000000000 : ℝ)*(sp7) + (1369762947758139/50000000000000 : ℝ)*(f.failure) + (2774905405292109/50000000000000 : ℝ)*(f.sum) + (805934017537/846250000000000000000000000 : ℝ)*base65 + (734626436979433/5289062500000000000000000000000 : ℝ)*base67 + (34088840144255741/10578125000000000000000000000000 : ℝ)*base69 + (15121015995619259/10578125000000000000000000000000 : ℝ)*base72 + (6312469147893/3385000000000000000000000000 : ℝ)*base73 + (135649605078943241/10578125000000000000000000000000 : ℝ)*base75 + (92883626255036991/10578125000000000000000000000000 : ℝ)*base77 + (108803631941036991/10578125000000000000000000000000 : ℝ)*base79 + (1452594824979/1692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1468043/1250000000000000000000 : ℝ)*base90 + (1468043/1250000000000000000000 : ℝ)*base92 + (1468043/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98974968883243999934979969/13222656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (223985539/50000000000000 : ℝ)*(base19) + (1027080911/100000000000000 : ℝ)*(base23) + (31298593/20000000000000 : ℝ)*(upper3) + (2318483/2000000000000 : ℝ)*(lower4) + (93691389/100000000000000 : ℝ)*(upper5) + (2087590991752699/50000000000000 : ℝ)*(major0) + (2087590991752699/50000000000000 : ℝ)*(major1) + (2087590991752699/50000000000000 : ℝ)*(major2) + (3816353319/50000000000000 : ℝ)*(sp1) + (9853599559/50000000000000 : ℝ)*(sp2) + (5590669148964831/100000000000000 : ℝ)*(sp4) + (1118132213657423/20000000000000 : ℝ)*(sp5) + (5590648414684803/100000000000000 : ℝ)*(sp6) + (137984728426871/5000000000000 : ℝ)*(sp7) + (137984728426871/5000000000000 : ℝ)*(f.failure) + (5590669148964831/100000000000000 : ℝ)*(f.sum) + (2621970305247/528906250000000000000000000 : ℝ)*base65 + (746017404776947729/105781250000000000000000000000000 : ℝ)*base68 + (191540965163353979/105781250000000000000000000000000 : ℝ)*base70 + (225043707086646021/105781250000000000000000000000000 : ℝ)*base71 + (70746253381129/16925000000000000000000000000 : ℝ)*base73 + (520729940020228979/105781250000000000000000000000000 : ℝ)*base76 + (949888315466635229/105781250000000000000000000000000 : ℝ)*base78 + (1698339981840072729/105781250000000000000000000000000 : ℝ)*base80 + (33516447124377/8462500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (148327/125000000000000000000 : ℝ)*base90 + (148327/125000000000000000000 : ℝ)*base92 + (148327/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1235_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s4_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122623303/10000000000 : ℝ)*x 0 + (5397777457/10000000000 : ℝ)*x 1 + (328815177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122623303/10000000000 : ℝ)^2107 ≤ (645307974213/5000000000000 : ℝ)^1595 := by
    have hnat : (2122623303 : ℕ)^2107*5000000000000^1595 ≤ 645307974213^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122623303 10000000000 645307974213 5000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397777457/10000000000 : ℝ)^2107 ≤ (110712116033/250000000000 : ℝ)^1595 := by
    have hnat : (5397777457 : ℕ)^2107*250000000000^1595 ≤ 110712116033^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397777457 10000000000 110712116033 250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328815177/625000000 : ℝ)^2107 ≤ (535112426083/1250000000000 : ℝ)^1595 := by
    have hnat : (328815177 : ℕ)^2107*1250000000000^1595 ≤ 535112426083^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328815177 625000000 535112426083 1250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122623303/10000000000 : ℝ), (5397777457/10000000000 : ℝ), (328815177/625000000 : ℝ)] ![(645307974213/5000000000000 : ℝ), (110712116033/250000000000 : ℝ), (535112426083/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122623303/10000000000 : ℝ)|^2107 ≤ (645307974213/5000000000000 : ℝ)^1595
        have hw : |(-2122623303/10000000000 : ℝ)|=(2122623303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397777457/10000000000 : ℝ)|^2107 ≤ (110712116033/250000000000 : ℝ)^1595
        have hw : |(5397777457/10000000000 : ℝ)|=(5397777457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328815177/625000000 : ℝ)|^2107 ≤ (535112426083/1250000000000 : ℝ)^1595
        have hw : |(328815177/625000000 : ℝ)|=(328815177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345976583/10000000000 : ℝ)*x 0 + (-2192049751/10000000000 : ℝ)*x 1 + (5261042823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345976583/10000000000 : ℝ)^2107 ≤ (43724301793247/100000000000000 : ℝ)^1595 := by
    have hnat : (5345976583 : ℕ)^2107*100000000000000^1595 ≤ 43724301793247^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345976583 10000000000 43724301793247 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192049751/10000000000 : ℝ)^2107 ≤ (538668168189/4000000000000 : ℝ)^1595 := by
    have hnat : (2192049751 : ℕ)^2107*4000000000000^1595 ≤ 538668168189^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192049751 10000000000 538668168189 4000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261042823/10000000000 : ℝ)^2107 ≤ (42808993989899/100000000000000 : ℝ)^1595 := by
    have hnat : (5261042823 : ℕ)^2107*100000000000000^1595 ≤ 42808993989899^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261042823 10000000000 42808993989899 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345976583/10000000000 : ℝ), (-2192049751/10000000000 : ℝ), (5261042823/10000000000 : ℝ)] ![(43724301793247/100000000000000 : ℝ), (538668168189/4000000000000 : ℝ), (42808993989899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345976583/10000000000 : ℝ)|^2107 ≤ (43724301793247/100000000000000 : ℝ)^1595
        have hw : |(5345976583/10000000000 : ℝ)|=(5345976583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192049751/10000000000 : ℝ)|^2107 ≤ (538668168189/4000000000000 : ℝ)^1595
        have hw : |(-2192049751/10000000000 : ℝ)|=(2192049751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261042823/10000000000 : ℝ)|^2107 ≤ (42808993989899/100000000000000 : ℝ)^1595
        have hw : |(5261042823/10000000000 : ℝ)|=(5261042823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345976597/10000000000 : ℝ)*x 0 + (5261042721/10000000000 : ℝ)*x 1 + (-2192049867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345976597/10000000000 : ℝ)^2107 ≤ (10931075486127/25000000000000 : ℝ)^1595 := by
    have hnat : (5345976597 : ℕ)^2107*25000000000000^1595 ≤ 10931075486127^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345976597 10000000000 10931075486127 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261042721/10000000000 : ℝ)^2107 ≤ (668890513961/1562500000000 : ℝ)^1595 := by
    have hnat : (5261042721 : ℕ)^2107*1562500000000^1595 ≤ 668890513961^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261042721 10000000000 668890513961 1562500000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192049867/10000000000 : ℝ)^2107 ≤ (6733352573061/50000000000000 : ℝ)^1595 := by
    have hnat : (2192049867 : ℕ)^2107*50000000000000^1595 ≤ 6733352573061^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192049867 10000000000 6733352573061 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345976597/10000000000 : ℝ), (5261042721/10000000000 : ℝ), (-2192049867/10000000000 : ℝ)] ![(10931075486127/25000000000000 : ℝ), (668890513961/1562500000000 : ℝ), (6733352573061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345976597/10000000000 : ℝ)|^2107 ≤ (10931075486127/25000000000000 : ℝ)^1595
        have hw : |(5345976597/10000000000 : ℝ)|=(5345976597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261042721/10000000000 : ℝ)|^2107 ≤ (668890513961/1562500000000 : ℝ)^1595
        have hw : |(5261042721/10000000000 : ℝ)|=(5261042721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192049867/10000000000 : ℝ)|^2107 ≤ (6733352573061/50000000000000 : ℝ)^1595
        have hw : |(-2192049867/10000000000 : ℝ)|=(2192049867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351401693/10000000000 : ℝ)*x 0 + (263440443/625000000 : ℝ)*x 1 + (1123012041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351401693/10000000000 : ℝ)^2107 ≤ (6662818835957/20000000000000 : ℝ)^1595 := by
    have hnat : (4351401693 : ℕ)^2107*20000000000000^1595 ≤ 6662818835957^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351401693 10000000000 6662818835957 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263440443/625000000 : ℝ)^2107 ≤ (15971026823343/50000000000000 : ℝ)^1595 := by
    have hnat : (263440443 : ℕ)^2107*50000000000000^1595 ≤ 15971026823343^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263440443 625000000 15971026823343 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123012041/2500000000 : ℝ)^2107 ≤ (1737192607943/5000000000000 : ℝ)^1595 := by
    have hnat : (1123012041 : ℕ)^2107*5000000000000^1595 ≤ 1737192607943^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123012041 2500000000 1737192607943 5000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351401693/10000000000 : ℝ), (263440443/625000000 : ℝ), (1123012041/2500000000 : ℝ)] ![(6662818835957/20000000000000 : ℝ), (15971026823343/50000000000000 : ℝ), (1737192607943/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351401693/10000000000 : ℝ)|^2107 ≤ (6662818835957/20000000000000 : ℝ)^1595
        have hw : |(4351401693/10000000000 : ℝ)|=(4351401693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263440443/625000000 : ℝ)|^2107 ≤ (15971026823343/50000000000000 : ℝ)^1595
        have hw : |(263440443/625000000 : ℝ)|=(263440443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123012041/2500000000 : ℝ)|^2107 ≤ (1737192607943/5000000000000 : ℝ)^1595
        have hw : |(1123012041/2500000000 : ℝ)|=(1123012041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122629291/10000000000 : ℝ)*x 0 + (5261422339/10000000000 : ℝ)*x 1 + (674674577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122629291/10000000000 : ℝ)^2107 ≤ (806637973773/6250000000000 : ℝ)^1595 := by
    have hnat : (2122629291 : ℕ)^2107*6250000000000^1595 ≤ 806637973773^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122629291 10000000000 806637973773 6250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261422339/10000000000 : ℝ)^2107 ≤ (2675817090309/6250000000000 : ℝ)^1595 := by
    have hnat : (5261422339 : ℕ)^2107*6250000000000^1595 ≤ 2675817090309^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261422339 10000000000 2675817090309 6250000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674674577/1250000000 : ℝ)^2107 ≤ (11070179738487/25000000000000 : ℝ)^1595 := by
    have hnat : (674674577 : ℕ)^2107*25000000000000^1595 ≤ 11070179738487^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674674577 1250000000 11070179738487 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122629291/10000000000 : ℝ), (5261422339/10000000000 : ℝ), (674674577/1250000000 : ℝ)] ![(806637973773/6250000000000 : ℝ), (2675817090309/6250000000000 : ℝ), (11070179738487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122629291/10000000000 : ℝ)|^2107 ≤ (806637973773/6250000000000 : ℝ)^1595
        have hw : |(-2122629291/10000000000 : ℝ)|=(2122629291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261422339/10000000000 : ℝ)|^2107 ≤ (2675817090309/6250000000000 : ℝ)^1595
        have hw : |(5261422339/10000000000 : ℝ)|=(5261422339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674674577/1250000000 : ℝ)|^2107 ≤ (11070179738487/25000000000000 : ℝ)^1595
        have hw : |(674674577/1250000000 : ℝ)|=(674674577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327776629/2500000000 : ℝ)*x 0 + (-102784809/500000000 : ℝ)*x 1 + (2698698209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327776629/2500000000 : ℝ)^2107 ≤ (21673973744809/50000000000000 : ℝ)^1595 := by
    have hnat : (1327776629 : ℕ)^2107*50000000000000^1595 ≤ 21673973744809^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327776629 2500000000 21673973744809 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102784809/500000000 : ℝ)^2107 ≤ (12371335686039/100000000000000 : ℝ)^1595 := by
    have hnat : (102784809 : ℕ)^2107*100000000000000^1595 ≤ 12371335686039^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102784809 500000000 12371335686039 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698698209/5000000000 : ℝ)^2107 ≤ (22140358404049/50000000000000 : ℝ)^1595 := by
    have hnat : (2698698209 : ℕ)^2107*50000000000000^1595 ≤ 22140358404049^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698698209 5000000000 22140358404049 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327776629/2500000000 : ℝ), (-102784809/500000000 : ℝ), (2698698209/5000000000 : ℝ)] ![(21673973744809/50000000000000 : ℝ), (12371335686039/100000000000000 : ℝ), (22140358404049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327776629/2500000000 : ℝ)|^2107 ≤ (21673973744809/50000000000000 : ℝ)^1595
        have hw : |(1327776629/2500000000 : ℝ)|=(1327776629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102784809/500000000 : ℝ)|^2107 ≤ (12371335686039/100000000000000 : ℝ)^1595
        have hw : |(-102784809/500000000 : ℝ)|=(102784809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698698209/5000000000 : ℝ)|^2107 ≤ (22140358404049/50000000000000 : ℝ)^1595
        have hw : |(2698698209/5000000000 : ℝ)|=(2698698209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311106001/10000000000 : ℝ)*x 0 + (2698698559/5000000000 : ℝ)*x 1 + (-82227837/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311106001/10000000000 : ℝ)^2107 ≤ (43347941937041/100000000000000 : ℝ)^1595 := by
    have hnat : (5311106001 : ℕ)^2107*100000000000000^1595 ≤ 43347941937041^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311106001 10000000000 43347941937041 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698698559/5000000000 : ℝ)^2107 ≤ (11070181098609/25000000000000 : ℝ)^1595 := by
    have hnat : (2698698559 : ℕ)^2107*25000000000000^1595 ≤ 11070181098609^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698698559 5000000000 11070181098609 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82227837/400000000 : ℝ)^2107 ≤ (2474266731763/20000000000000 : ℝ)^1595 := by
    have hnat : (82227837 : ℕ)^2107*20000000000000^1595 ≤ 2474266731763^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82227837 400000000 2474266731763 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311106001/10000000000 : ℝ), (2698698559/5000000000 : ℝ), (-82227837/400000000 : ℝ)] ![(43347941937041/100000000000000 : ℝ), (11070181098609/25000000000000 : ℝ), (2474266731763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311106001/10000000000 : ℝ)|^2107 ≤ (43347941937041/100000000000000 : ℝ)^1595
        have hw : |(5311106001/10000000000 : ℝ)|=(5311106001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698698559/5000000000 : ℝ)|^2107 ≤ (11070181098609/25000000000000 : ℝ)^1595
        have hw : |(2698698559/5000000000 : ℝ)|=(2698698559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82227837/400000000 : ℝ)|^2107 ≤ (2474266731763/20000000000000 : ℝ)^1595
        have hw : |(-82227837/400000000 : ℝ)|=(82227837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s4_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (870282879/2000000000 : ℝ)*x 0 + (280705003/625000000 : ℝ)*x 1 + (2107909091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870282879/2000000000 : ℝ)^2107 ≤ (16657111320939/50000000000000 : ℝ)^1595 := by
    have hnat : (870282879 : ℕ)^2107*50000000000000^1595 ≤ 16657111320939^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870282879 2000000000 16657111320939 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280705003/625000000 : ℝ)^2107 ≤ (34736004279753/100000000000000 : ℝ)^1595 := by
    have hnat : (280705003 : ℕ)^2107*100000000000000^1595 ≤ 34736004279753^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280705003 625000000 34736004279753 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107909091/5000000000 : ℝ)^2107 ≤ (15974886530289/50000000000000 : ℝ)^1595 := by
    have hnat : (2107909091 : ℕ)^2107*50000000000000^1595 ≤ 15974886530289^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107909091 5000000000 15974886530289 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870282879/2000000000 : ℝ), (280705003/625000000 : ℝ), (2107909091/5000000000 : ℝ)] ![(16657111320939/50000000000000 : ℝ), (34736004279753/100000000000000 : ℝ), (15974886530289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870282879/2000000000 : ℝ)|^2107 ≤ (16657111320939/50000000000000 : ℝ)^1595
        have hw : |(870282879/2000000000 : ℝ)|=(870282879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280705003/625000000 : ℝ)|^2107 ≤ (34736004279753/100000000000000 : ℝ)^1595
        have hw : |(280705003/625000000 : ℝ)|=(280705003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107909091/5000000000 : ℝ)|^2107 ≤ (15974886530289/50000000000000 : ℝ)^1595
        have hw : |(2107909091/5000000000 : ℝ)|=(2107909091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (567/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10893/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (218341579337729/2000000000000000000 : ℝ) := by
    have hpowers : (10893/100000 : ℝ)^8427 ≤ (218341579337729/2000000000000000000 : ℝ)^2048 := by
      have hnat : (10893 : ℕ)^8427*2000000000000000000^2048 ≤ 218341579337729^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10893 100000 218341579337729 2000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10893/100000 : ℝ)) (X := (218341579337729/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14707/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (37546807074632781/100000000000000000000 : ℝ) := by
    have hpowers : (14707/100000 : ℝ)^8427 ≤ (37546807074632781/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14707 : ℕ)^8427*100000000000000000000^2048 ≤ 37546807074632781^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14707 100000 37546807074632781 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14707/100000 : ℝ)) (X := (37546807074632781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000218341579337729/1000000000000000000 : ℝ) ≤ (10000530588116737/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (1000218341579337729/1000000000000000000 : ℝ)^2048 ≤ (10000530588116737/10000000000000000 : ℝ)^8427 := by
      have hnat : (1000218341579337729 : ℕ)^2048*10000000000000000^8427 ≤ 10000530588116737^8427*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000218341579337729 1000000000000000000 10000530588116737 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000530588116737/10000000000000000 : ℝ)) (X := (1000218341579337729/1000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048463886041519231/100000000000000000000 : ℝ) ≤ (10001177593897189/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100048463886041519231/100000000000000000000 : ℝ)^2048 ≤ (10001177593897189/10000000000000000 : ℝ)^8427 := by
      have hnat : (100048463886041519231 : ℕ)^2048*10000000000000000^8427 ≤ 10001177593897189^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048463886041519231 100000000000000000000 10001177593897189 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177593897189/10000000000000000 : ℝ)) (X := (100048463886041519231/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037546807074632781/50000000000000000000 : ℝ) ≤ (10001824599677641/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50037546807074632781/50000000000000000000 : ℝ)^2048 ≤ (10001824599677641/10000000000000000 : ℝ)^8427 := by
      have hnat : (50037546807074632781 : ℕ)^2048*10000000000000000^8427 ≤ 10001824599677641^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037546807074632781 50000000000000000000 10001824599677641 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001824599677641/10000000000000000 : ℝ)) (X := (50037546807074632781/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(218341579337729/2000000000000000000 : ℝ) ≤ ((19063963997572153823/19070000000000000000 : ℝ)+2*(161751445113/95350000000000 : ℝ)*(10893/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (19063963997572153823/19070000000000000000 : ℝ)+2*(161751445113/95350000000000 : ℝ)*(10893/100000 : ℝ)=(10000530588116737/10000000000000000 : ℝ) by norm_num, show 1+2*(218341579337729/2000000000000000000 : ℝ)=(1000218341579337729/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37546807074632781/100000000000000000000 : ℝ)+(218341579337729/2000000000000000000 : ℝ) ≤ ((19063963997572153823/19070000000000000000 : ℝ)+(161751445113/95350000000000 : ℝ)*((14707/100000 : ℝ)+(10893/100000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (19063963997572153823/19070000000000000000 : ℝ)+(161751445113/95350000000000 : ℝ)*((14707/100000 : ℝ)+(10893/100000 : ℝ))=(10001177593897189/10000000000000000 : ℝ) by norm_num, show 1+(37546807074632781/100000000000000000000 : ℝ)+(218341579337729/2000000000000000000 : ℝ)=(100048463886041519231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37546807074632781/100000000000000000000 : ℝ) ≤ ((19063963997572153823/19070000000000000000 : ℝ)+2*(161751445113/95350000000000 : ℝ)*(14707/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (19063963997572153823/19070000000000000000 : ℝ)+2*(161751445113/95350000000000 : ℝ)*(14707/100000 : ℝ)=(10001824599677641/10000000000000000 : ℝ) by norm_num, show 1+2*(37546807074632781/100000000000000000000 : ℝ)=(50037546807074632781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19063963997572153823/19070000000000000000 : ℝ)*(X 1 0+X 2 0)+(161751445113/95350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (19063963997572153823/19070000000000000000 : ℝ)) (alpha := (161751445113/95350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19063963997572153823/19070000000000000000 : ℝ)*(X 0 1+X 2 1)+(161751445113/95350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (19063963997572153823/19070000000000000000 : ℝ)) (alpha := (161751445113/95350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19063963997572153823/19070000000000000000 : ℝ)*(X 0 2+X 1 2)+(161751445113/95350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (19063963997572153823/19070000000000000000 : ℝ)) (alpha := (161751445113/95350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2122623303/10000000000 : ℝ)*X 0 0+(5397777457/10000000000 : ℝ)*X 0 1+(328815177/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345976583/10000000000 : ℝ)*X 1 0+(-2192049751/10000000000 : ℝ)*X 1 1+(5261042823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345976597/10000000000 : ℝ)*X 2 0+(5261042721/10000000000 : ℝ)*X 2 1+(-2192049867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351401693/10000000000 : ℝ)*X 0 0+(263440443/625000000 : ℝ)*X 0 1+(1123012041/2500000000 : ℝ)*X 0 2+(4351401693/10000000000 : ℝ)*X 1 0+(263440443/625000000 : ℝ)*X 1 1+(1123012041/2500000000 : ℝ)*X 1 2+(4351401693/10000000000 : ℝ)*X 2 0+(263440443/625000000 : ℝ)*X 2 1+(1123012041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122629291/10000000000 : ℝ)*X 0 0+(5261422339/10000000000 : ℝ)*X 0 1+(674674577/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327776629/2500000000 : ℝ)*X 1 0+(-102784809/500000000 : ℝ)*X 1 1+(2698698209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311106001/10000000000 : ℝ)*X 2 0+(2698698559/5000000000 : ℝ)*X 2 1+(-82227837/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870282879/2000000000 : ℝ)*X 0 0+(280705003/625000000 : ℝ)*X 0 1+(2107909091/5000000000 : ℝ)*X 0 2+(870282879/2000000000 : ℝ)*X 1 0+(280705003/625000000 : ℝ)*X 1 1+(2107909091/5000000000 : ℝ)*X 1 2+(870282879/2000000000 : ℝ)*X 2 0+(280705003/625000000 : ℝ)*X 2 1+(2107909091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3800952304018829367420903489/476750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2014974713/100000000000000 : ℝ)*(base19) + (966693983/50000000000000 : ℝ)*(base23) + (10762637/3125000000000 : ℝ)*(upper3) + (53855027/100000000000000 : ℝ)*(upper4) + (100465987/100000000000000 : ℝ)*(upper5) + (5461839367310581/100000000000000 : ℝ)*(major0) + (5461839367310581/100000000000000 : ℝ)*(major1) + (5461839367310581/100000000000000 : ℝ)*(major2) + (7313490119804709/100000000000000 : ℝ)*(sp0) + (7313532394126797/100000000000000 : ℝ)*(sp1) + (914191559464193/12500000000000 : ℝ)*(sp2) + (1805058272179769/50000000000000 : ℝ)*(sp3) + (44289296801/100000000000000 : ℝ)*(sp4) + (27515405703/100000000000000 : ℝ)*(sp7) + (1805072029882621/50000000000000 : ℝ)*(f.failure) + (731353440910151/10000000000000 : ℝ)*(f.sum) + (5827324450771/9535000000000000000000000000 : ℝ)*base65 + (31233175132201898837/1907000000000000000000000000000000 : ℝ)*base68 + (5901502190895898837/1907000000000000000000000000000000 : ℝ)*base70 + (7383068502088101163/1907000000000000000000000000000000 : ℝ)*base71 + (12570467012129/9535000000000000000000000000 : ℝ)*base74 + (41080897328584898837/1907000000000000000000000000000000 : ℝ)*base76 + (37631924166030898837/1907000000000000000000000000000000 : ℝ)*base78 + (2775072623705898837/1907000000000000000000000000000000 : ℝ)*base80 + (22047852098189/2383750000000000000000000000 : ℝ)*base81 + (17663923/1250000000000000000000 : ℝ)*base89 + (17663923/1250000000000000000000 : ℝ)*base91 + (17663923/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2177793565952741790472671501/476750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536585559/100000000000000 : ℝ)*(base19) + (8314989/20000000000000 : ℝ)*(lower2) + (12669183/12500000000000 : ℝ)*(upper3) + (17451841/20000000000000 : ℝ)*(lower4) + (29629289/50000000000000 : ℝ)*(upper5) + (5492300866868129/100000000000000 : ℝ)*(major0) + (5492300866868129/100000000000000 : ℝ)*(major1) + (5492300866868129/100000000000000 : ℝ)*(major2) + (13787283551/100000000000000 : ℝ)*(sp2) + (713584599/10000000000000 : ℝ)*(sp3) + (3677161602676737/50000000000000 : ℝ)*(sp4) + (1470864533753583/20000000000000 : ℝ)*(sp5) + (7354309418069923/100000000000000 : ℝ)*(sp6) + (72605424805403/2000000000000 : ℝ)*(sp7) + (181513918805807/5000000000000 : ℝ)*(f.failure) + (3677161602676737/50000000000000 : ℝ)*(f.sum) + (972228905411/2383750000000000000000000000 : ℝ)*base65 + (11663409583682392833/1907000000000000000000000000000000 : ℝ)*base68 + (15385823311348392833/1907000000000000000000000000000000 : ℝ)*base70 + (29495393677460392833/1907000000000000000000000000000000 : ℝ)*base72 + (30797856084773/4767500000000000000000000000 : ℝ)*base74 + (20383995973849607167/1907000000000000000000000000000000 : ℝ)*base75 + (34613266272570392833/1907000000000000000000000000000000 : ℝ)*base78 + (2851941591275392833/1907000000000000000000000000000000 : ℝ)*base80 + (27805051037363/4767500000000000000000000000 : ℝ)*base82 + (515441/125000000000000000000 : ℝ)*base89 + (515441/125000000000000000000 : ℝ)*base91 + (515441/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1235_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s5_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123084469/10000000000 : ℝ)*x 0 + (5392576717/10000000000 : ℝ)*x 1 + (1316485107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123084469/10000000000 : ℝ)^2107 ≤ (3227465933741/25000000000000 : ℝ)^1595 := by
    have hnat : (2123084469 : ℕ)^2107*25000000000000^1595 ≤ 3227465933741^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123084469 10000000000 3227465933741 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392576717/10000000000 : ℝ)^2107 ≤ (1769139607093/4000000000000 : ℝ)^1595 := by
    have hnat : (5392576717 : ℕ)^2107*4000000000000^1595 ≤ 1769139607093^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392576717 10000000000 1769139607093 4000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316485107/2500000000 : ℝ)^2107 ≤ (8572329217077/20000000000000 : ℝ)^1595 := by
    have hnat : (1316485107 : ℕ)^2107*20000000000000^1595 ≤ 8572329217077^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316485107 2500000000 8572329217077 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123084469/10000000000 : ℝ), (5392576717/10000000000 : ℝ), (1316485107/2500000000 : ℝ)] ![(3227465933741/25000000000000 : ℝ), (1769139607093/4000000000000 : ℝ), (8572329217077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123084469/10000000000 : ℝ)|^2107 ≤ (3227465933741/25000000000000 : ℝ)^1595
        have hw : |(-2123084469/10000000000 : ℝ)|=(2123084469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392576717/10000000000 : ℝ)|^2107 ≤ (1769139607093/4000000000000 : ℝ)^1595
        have hw : |(5392576717/10000000000 : ℝ)|=(5392576717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316485107/2500000000 : ℝ)|^2107 ≤ (8572329217077/20000000000000 : ℝ)^1595
        have hw : |(1316485107/2500000000 : ℝ)|=(1316485107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344661283/10000000000 : ℝ)*x 0 + (-68353479/312500000 : ℝ)*x 1 + (658242549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344661283/10000000000 : ℝ)^2107 ≤ (21855045679519/50000000000000 : ℝ)^1595 := by
    have hnat : (5344661283 : ℕ)^2107*50000000000000^1595 ≤ 21855045679519^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344661283 10000000000 21855045679519 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68353479/312500000 : ℝ)^2107 ≤ (6714131463557/50000000000000 : ℝ)^1595 := by
    have hnat : (68353479 : ℕ)^2107*50000000000000^1595 ≤ 6714131463557^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68353479 312500000 6714131463557 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658242549/1250000000 : ℝ)^2107 ≤ (21430822849153/50000000000000 : ℝ)^1595 := by
    have hnat : (658242549 : ℕ)^2107*50000000000000^1595 ≤ 21430822849153^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658242549 1250000000 21430822849153 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344661283/10000000000 : ℝ), (-68353479/312500000 : ℝ), (658242549/1250000000 : ℝ)] ![(21855045679519/50000000000000 : ℝ), (6714131463557/50000000000000 : ℝ), (21430822849153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344661283/10000000000 : ℝ)|^2107 ≤ (21855045679519/50000000000000 : ℝ)^1595
        have hw : |(5344661283/10000000000 : ℝ)|=(5344661283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68353479/312500000 : ℝ)|^2107 ≤ (6714131463557/50000000000000 : ℝ)^1595
        have hw : |(-68353479/312500000 : ℝ)|=(68353479/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658242549/1250000000 : ℝ)|^2107 ≤ (21430822849153/50000000000000 : ℝ)^1595
        have hw : |(658242549/1250000000 : ℝ)|=(658242549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8351033/15625000 : ℝ)*x 0 + (1053188069/2000000000 : ℝ)*x 1 + (-2187311607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8351033/15625000 : ℝ)^2107 ≤ (43710089598063/100000000000000 : ℝ)^1595 := by
    have hnat : (8351033 : ℕ)^2107*100000000000000^1595 ≤ 43710089598063^1595*15625000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8351033 15625000 43710089598063 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053188069/2000000000 : ℝ)^2107 ≤ (42861645192953/100000000000000 : ℝ)^1595 := by
    have hnat : (1053188069 : ℕ)^2107*100000000000000^1595 ≤ 42861645192953^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053188069 2000000000 42861645192953 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187311607/10000000000 : ℝ)^2107 ≤ (3357066297441/25000000000000 : ℝ)^1595 := by
    have hnat : (2187311607 : ℕ)^2107*25000000000000^1595 ≤ 3357066297441^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187311607 10000000000 3357066297441 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8351033/15625000 : ℝ), (1053188069/2000000000 : ℝ), (-2187311607/10000000000 : ℝ)] ![(43710089598063/100000000000000 : ℝ), (42861645192953/100000000000000 : ℝ), (3357066297441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8351033/15625000 : ℝ)|^2107 ≤ (43710089598063/100000000000000 : ℝ)^1595
        have hw : |(8351033/15625000 : ℝ)|=(8351033/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053188069/2000000000 : ℝ)|^2107 ≤ (42861645192953/100000000000000 : ℝ)^1595
        have hw : |(1053188069/2000000000 : ℝ)|=(1053188069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187311607/10000000000 : ℝ)|^2107 ≤ (3357066297441/25000000000000 : ℝ)^1595
        have hw : |(-2187311607/10000000000 : ℝ)|=(2187311607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4351672197/10000000000 : ℝ)*x 0 + (1056310211/2500000000 : ℝ)*x 1 + (4481785167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351672197/10000000000 : ℝ)^2107 ≤ (16658414978429/50000000000000 : ℝ)^1595 := by
    have hnat : (4351672197 : ℕ)^2107*50000000000000^1595 ≤ 16658414978429^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351672197 10000000000 16658414978429 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056310211/2500000000 : ℝ)^2107 ≤ (250344842367/781250000000 : ℝ)^1595 := by
    have hnat : (1056310211 : ℕ)^2107*781250000000^1595 ≤ 250344842367^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056310211 2500000000 250344842367 781250000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481785167/10000000000 : ℝ)^2107 ≤ (8659757551431/25000000000000 : ℝ)^1595 := by
    have hnat : (4481785167 : ℕ)^2107*25000000000000^1595 ≤ 8659757551431^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481785167 10000000000 8659757551431 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351672197/10000000000 : ℝ), (1056310211/2500000000 : ℝ), (4481785167/10000000000 : ℝ)] ![(16658414978429/50000000000000 : ℝ), (250344842367/781250000000 : ℝ), (8659757551431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351672197/10000000000 : ℝ)|^2107 ≤ (16658414978429/50000000000000 : ℝ)^1595
        have hw : |(4351672197/10000000000 : ℝ)|=(4351672197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056310211/2500000000 : ℝ)|^2107 ≤ (250344842367/781250000000 : ℝ)^1595
        have hw : |(1056310211/2500000000 : ℝ)|=(1056310211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481785167/10000000000 : ℝ)|^2107 ≤ (8659757551431/25000000000000 : ℝ)^1595
        have hw : |(4481785167/10000000000 : ℝ)|=(4481785167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-66346547/312500000 : ℝ)*x 0 + (1316566441/2500000000 : ℝ)*x 1 + (2696125057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66346547/312500000 : ℝ)^2107 ≤ (2581980835863/20000000000000 : ℝ)^1595 := by
    have hnat : (66346547 : ℕ)^2107*20000000000000^1595 ≤ 2581980835863^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66346547 312500000 2581980835863 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316566441/2500000000 : ℝ)^2107 ≤ (68584230709/160000000000 : ℝ)^1595 := by
    have hnat : (1316566441 : ℕ)^2107*160000000000^1595 ≤ 68584230709^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316566441 2500000000 68584230709 160000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696125057/5000000000 : ℝ)^2107 ≤ (44224951625359/100000000000000 : ℝ)^1595 := by
    have hnat : (2696125057 : ℕ)^2107*100000000000000^1595 ≤ 44224951625359^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696125057 5000000000 44224951625359 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66346547/312500000 : ℝ), (1316566441/2500000000 : ℝ), (2696125057/5000000000 : ℝ)] ![(2581980835863/20000000000000 : ℝ), (68584230709/160000000000 : ℝ), (44224951625359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66346547/312500000 : ℝ)|^2107 ≤ (2581980835863/20000000000000 : ℝ)^1595
        have hw : |(-66346547/312500000 : ℝ)|=(66346547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316566441/2500000000 : ℝ)|^2107 ≤ (68584230709/160000000000 : ℝ)^1595
        have hw : |(1316566441/2500000000 : ℝ)|=(1316566441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696125057/5000000000 : ℝ)|^2107 ≤ (44224951625359/100000000000000 : ℝ)^1595
        have hw : |(2696125057/5000000000 : ℝ)|=(2696125057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664045627/1250000000 : ℝ)*x 0 + (-412200341/2000000000 : ℝ)*x 1 + (5392250119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664045627/1250000000 : ℝ)^2107 ≤ (5420189597401/12500000000000 : ℝ)^1595 := by
    have hnat : (664045627 : ℕ)^2107*12500000000000^1595 ≤ 5420189597401^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664045627 1250000000 5420189597401 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412200341/2000000000 : ℝ)^2107 ≤ (12413531525811/100000000000000 : ℝ)^1595 := by
    have hnat : (412200341 : ℕ)^2107*100000000000000^1595 ≤ 12413531525811^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412200341 2000000000 12413531525811 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392250119/10000000000 : ℝ)^2107 ≤ (4422495167953/10000000000000 : ℝ)^1595 := by
    have hnat : (5392250119 : ℕ)^2107*10000000000000^1595 ≤ 4422495167953^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392250119 10000000000 4422495167953 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664045627/1250000000 : ℝ), (-412200341/2000000000 : ℝ), (5392250119/10000000000 : ℝ)] ![(5420189597401/12500000000000 : ℝ), (12413531525811/100000000000000 : ℝ), (4422495167953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664045627/1250000000 : ℝ)|^2107 ≤ (5420189597401/12500000000000 : ℝ)^1595
        have hw : |(664045627/1250000000 : ℝ)|=(664045627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412200341/2000000000 : ℝ)|^2107 ≤ (12413531525811/100000000000000 : ℝ)^1595
        have hw : |(-412200341/2000000000 : ℝ)|=(412200341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392250119/10000000000 : ℝ)|^2107 ≤ (4422495167953/10000000000000 : ℝ)^1595
        have hw : |(5392250119/10000000000 : ℝ)|=(5392250119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312365017/10000000000 : ℝ)*x 0 + (1348062529/2500000000 : ℝ)*x 1 + (-2061001709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312365017/10000000000 : ℝ)^2107 ≤ (43361516789991/100000000000000 : ℝ)^1595 := by
    have hnat : (5312365017 : ℕ)^2107*100000000000000^1595 ≤ 43361516789991^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312365017 10000000000 43361516789991 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348062529/2500000000 : ℝ)^2107 ≤ (44224951647027/100000000000000 : ℝ)^1595 := by
    have hnat : (1348062529 : ℕ)^2107*100000000000000^1595 ≤ 44224951647027^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348062529 2500000000 44224951647027 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061001709/10000000000 : ℝ)^2107 ≤ (12413531557637/100000000000000 : ℝ)^1595 := by
    have hnat : (2061001709 : ℕ)^2107*100000000000000^1595 ≤ 12413531557637^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061001709 10000000000 12413531557637 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312365017/10000000000 : ℝ), (1348062529/2500000000 : ℝ), (-2061001709/10000000000 : ℝ)] ![(43361516789991/100000000000000 : ℝ), (44224951647027/100000000000000 : ℝ), (12413531557637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312365017/10000000000 : ℝ)|^2107 ≤ (43361516789991/100000000000000 : ℝ)^1595
        have hw : |(5312365017/10000000000 : ℝ)|=(5312365017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348062529/2500000000 : ℝ)|^2107 ≤ (44224951647027/100000000000000 : ℝ)^1595
        have hw : |(1348062529/2500000000 : ℝ)|=(1348062529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061001709/10000000000 : ℝ)|^2107 ≤ (12413531557637/100000000000000 : ℝ)^1595
        have hw : |(-2061001709/10000000000 : ℝ)|=(2061001709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s5_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (543960267/1250000000 : ℝ)*x 0 + (89622513/200000000 : ℝ)*x 1 + (4225902893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543960267/1250000000 : ℝ)^2107 ≤ (4164616309657/12500000000000 : ℝ)^1595 := by
    have hnat : (543960267 : ℕ)^2107*12500000000000^1595 ≤ 4164616309657^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543960267 1250000000 4164616309657 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89622513/200000000 : ℝ)^2107 ≤ (34632296807897/100000000000000 : ℝ)^1595 := by
    have hnat : (89622513 : ℕ)^2107*100000000000000^1595 ≤ 34632296807897^1595*200000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89622513 200000000 34632296807897 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225902893/10000000000 : ℝ)^2107 ≤ (16025386350817/50000000000000 : ℝ)^1595 := by
    have hnat : (4225902893 : ℕ)^2107*50000000000000^1595 ≤ 16025386350817^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225902893 10000000000 16025386350817 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543960267/1250000000 : ℝ), (89622513/200000000 : ℝ), (4225902893/10000000000 : ℝ)] ![(4164616309657/12500000000000 : ℝ), (34632296807897/100000000000000 : ℝ), (16025386350817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543960267/1250000000 : ℝ)|^2107 ≤ (4164616309657/12500000000000 : ℝ)^1595
        have hw : |(543960267/1250000000 : ℝ)|=(543960267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89622513/200000000 : ℝ)|^2107 ≤ (34632296807897/100000000000000 : ℝ)^1595
        have hw : |(89622513/200000000 : ℝ)|=(89622513/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225902893/10000000000 : ℝ)|^2107 ≤ (16025386350817/50000000000000 : ℝ)^1595
        have hw : |(4225902893/10000000000 : ℝ)|=(4225902893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2289/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (567/5000 : ℝ) ^ (8427/2048 : ℝ) ≤ (12881687495960849/100000000000000000000 : ℝ) := by
    have hpowers : (567/5000 : ℝ)^8427 ≤ (12881687495960849/100000000000000000000 : ℝ)^2048 := by
      have hnat : (567 : ℕ)^8427*100000000000000000000^2048 ≤ 12881687495960849^2048*5000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        567 5000 12881687495960849 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (567/5000 : ℝ)) (X := (12881687495960849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8427/2048 : ℝ) ≤ (16420126529721317/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8427 ≤ (16420126529721317/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8427*50000000000000000000^2048 ≤ 16420126529721317^2048*25000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 16420126529721317 50000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (16420126529721317/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012881687495960849/50000000000000000000 : ℝ) ≤ (2500156515508969/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50012881687495960849/50000000000000000000 : ℝ)^2048 ≤ (2500156515508969/2500000000000000 : ℝ)^8427 := by
      have hnat : (50012881687495960849 : ℕ)^2048*2500000000000000^8427 ≤ 2500156515508969^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012881687495960849 50000000000000000000 2500156515508969 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500156515508969/2500000000000000 : ℝ)) (X := (50012881687495960849/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045721940555403483/100000000000000000000 : ℝ) ≤ (5000555490295167/5000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100045721940555403483/100000000000000000000 : ℝ)^2048 ≤ (5000555490295167/5000000000000000 : ℝ)^8427 := by
      have hnat : (100045721940555403483 : ℕ)^2048*5000000000000000^8427 ≤ 5000555490295167^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045721940555403483 100000000000000000000 5000555490295167 5000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000555490295167/5000000000000000 : ℝ)) (X := (100045721940555403483/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016420126529721317/25000000000000000000 : ℝ) ≤ (1250199487393099/1250000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25016420126529721317/25000000000000000000 : ℝ)^2048 ≤ (1250199487393099/1250000000000000 : ℝ)^8427 := by
      have hnat : (25016420126529721317 : ℕ)^2048*1250000000000000^8427 ≤ 1250199487393099^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016420126529721317 25000000000000000000 1250199487393099 1250000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250199487393099/1250000000000000 : ℝ)) (X := (25016420126529721317/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12881687495960849/100000000000000000000 : ℝ) ≤ ((1809425945177549341/1810000000000000000 : ℝ)+2*(242459277229/144800000000000 : ℝ)*(567/5000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1809425945177549341/1810000000000000000 : ℝ)+2*(242459277229/144800000000000 : ℝ)*(567/5000 : ℝ)=(2500156515508969/2500000000000000 : ℝ) by norm_num, show 1+2*(12881687495960849/100000000000000000000 : ℝ)=(50012881687495960849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16420126529721317/50000000000000000000 : ℝ)+(12881687495960849/100000000000000000000 : ℝ) ≤ ((1809425945177549341/1810000000000000000 : ℝ)+(242459277229/144800000000000 : ℝ)*((3559/25000 : ℝ)+(567/5000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (1809425945177549341/1810000000000000000 : ℝ)+(242459277229/144800000000000 : ℝ)*((3559/25000 : ℝ)+(567/5000 : ℝ))=(5000555490295167/5000000000000000 : ℝ) by norm_num, show 1+(16420126529721317/50000000000000000000 : ℝ)+(12881687495960849/100000000000000000000 : ℝ)=(100045721940555403483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16420126529721317/50000000000000000000 : ℝ) ≤ ((1809425945177549341/1810000000000000000 : ℝ)+2*(242459277229/144800000000000 : ℝ)*(3559/25000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1809425945177549341/1810000000000000000 : ℝ)+2*(242459277229/144800000000000 : ℝ)*(3559/25000 : ℝ)=(1250199487393099/1250000000000000 : ℝ) by norm_num, show 1+2*(16420126529721317/50000000000000000000 : ℝ)=(25016420126529721317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1809425945177549341/1810000000000000000 : ℝ)*(X 1 0+X 2 0)+(242459277229/144800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1809425945177549341/1810000000000000000 : ℝ)) (alpha := (242459277229/144800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1809425945177549341/1810000000000000000 : ℝ)*(X 0 1+X 2 1)+(242459277229/144800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1809425945177549341/1810000000000000000 : ℝ)) (alpha := (242459277229/144800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1809425945177549341/1810000000000000000 : ℝ)*(X 0 2+X 1 2)+(242459277229/144800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1809425945177549341/1810000000000000000 : ℝ)) (alpha := (242459277229/144800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123084469/10000000000 : ℝ)*X 0 0+(5392576717/10000000000 : ℝ)*X 0 1+(1316485107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344661283/10000000000 : ℝ)*X 1 0+(-68353479/312500000 : ℝ)*X 1 1+(658242549/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8351033/15625000 : ℝ)*X 2 0+(1053188069/2000000000 : ℝ)*X 2 1+(-2187311607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351672197/10000000000 : ℝ)*X 0 0+(1056310211/2500000000 : ℝ)*X 0 1+(4481785167/10000000000 : ℝ)*X 0 2+(4351672197/10000000000 : ℝ)*X 1 0+(1056310211/2500000000 : ℝ)*X 1 1+(4481785167/10000000000 : ℝ)*X 1 2+(4351672197/10000000000 : ℝ)*X 2 0+(1056310211/2500000000 : ℝ)*X 2 1+(4481785167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-66346547/312500000 : ℝ)*X 0 0+(1316566441/2500000000 : ℝ)*X 0 1+(2696125057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664045627/1250000000 : ℝ)*X 1 0+(-412200341/2000000000 : ℝ)*X 1 1+(5392250119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312365017/10000000000 : ℝ)*X 2 0+(1348062529/2500000000 : ℝ)*X 2 1+(-2061001709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543960267/1250000000 : ℝ)*X 0 0+(89622513/200000000 : ℝ)*X 0 1+(4225902893/10000000000 : ℝ)*X 0 2+(543960267/1250000000 : ℝ)*X 1 0+(89622513/200000000 : ℝ)*X 1 1+(4225902893/10000000000 : ℝ)*X 1 2+(543960267/1250000000 : ℝ)*X 2 0+(89622513/200000000 : ℝ)*X 2 1+(4225902893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7334510535152869041882891/2262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52341679/10000000000000 : ℝ)*(base19) + (229021397/50000000000000 : ℝ)*(base23) + (100682943/100000000000000 : ℝ)*(upper3) + (61609153/50000000000000 : ℝ)*(lower4) + (294866276833233/5000000000000 : ℝ)*(major0) + (294866276833233/5000000000000 : ℝ)*(major1) + (294866276833233/5000000000000 : ℝ)*(major2) + (1579330331501377/20000000000000 : ℝ)*(sp0) + (7896660529862461/100000000000000 : ℝ)*(sp1) + (3948325739340089/50000000000000 : ℝ)*(sp2) + (974494060812487/25000000000000 : ℝ)*(sp3) + (4697886183/50000000000000 : ℝ)*(sp4) + (227913907/2500000000000 : ℝ)*(sp6) + (13668741021/100000000000000 : ℝ)*(sp7) + (389798991199097/10000000000000 : ℝ)*(f.failure) + (1974165263319813/25000000000000 : ℝ)*(f.sum) + (1306459199311/362000000000000000000000000 : ℝ)*base65 + (70808378652461953/9050000000000000000000000000000 : ℝ)*base67 + (42212617242361953/9050000000000000000000000000000 : ℝ)*base69 + (135208584599261953/9050000000000000000000000000000 : ℝ)*base71 + (675862021191/362000000000000000000000000 : ℝ)*base74 + (55850711959961953/9050000000000000000000000000000 : ℝ)*base75 + (17258679753411953/9050000000000000000000000000000 : ℝ)*base77 + (212558304622588047/9050000000000000000000000000000 : ℝ)*base80 + (3102413162729/362000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1554711/250000000000000000000 : ℝ)*base89 + (1554711/250000000000000000000 : ℝ)*base91 + (1554711/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86045576406557191505260617/22625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138278969/20000000000000 : ℝ)*(base19) + (186913817/25000000000000 : ℝ)*(base23) + (19033787/25000000000000 : ℝ)*(upper3) + (5083543/20000000000000 : ℝ)*(lower4) + (7651099/10000000000000 : ℝ)*(upper5) + (1481954863611679/25000000000000 : ℝ)*(major0) + (1481954863611679/25000000000000 : ℝ)*(major1) + (1481954863611679/25000000000000 : ℝ)*(major2) + (3901695593/20000000000000 : ℝ)*(sp1) + (20646833673/100000000000000 : ℝ)*(sp2) + (793749312611657/10000000000000 : ℝ)*(sp4) + (99218411578047/1250000000000 : ℝ)*(sp5) + (7937471731627629/100000000000000 : ℝ)*(sp6) + (61221025875097/1562500000000 : ℝ)*(sp7) + (61221025875097/1562500000000 : ℝ)*(f.failure) + (793749312611657/10000000000000 : ℝ)*(f.sum) + (10461443246989/1810000000000000000000000000 : ℝ)*base66 + (140246903815008961/45250000000000000000000000000000 : ℝ)*base68 + (421683986806008961/45250000000000000000000000000000 : ℝ)*base70 + (582148668865758961/45250000000000000000000000000000 : ℝ)*base72 + (1614301404691/1810000000000000000000000000 : ℝ)*base73 + (734060709708991039/45250000000000000000000000000000 : ℝ)*base75 + (276879462575258961/45250000000000000000000000000000 : ℝ)*base78 + (238261080412741039/45250000000000000000000000000000 : ℝ)*base79 + (2008707524829/1810000000000000000000000000 : ℝ)*base82 + (505211/39062500000000000000 : ℝ)*base89 + (505211/39062500000000000000 : ℝ)*base91 + (505211/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1235_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1235_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1235_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1235_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1235_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
