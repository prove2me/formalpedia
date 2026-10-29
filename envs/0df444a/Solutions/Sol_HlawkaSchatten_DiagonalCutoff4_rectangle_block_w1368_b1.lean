-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:40.074172+00:00
-- url     : https://prove2.me/submissions/fb91aeb9-f479-4a7e-abe5-41bf5943341e

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
theorem support_rectangle_w1368_s3_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020208043/10000000000 : ℝ)*x 0 + (2711981911/5000000000 : ℝ)*x 1 + (5233768611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020208043/10000000000 : ℝ)^541 ≤ (3076517215787/25000000000000 : ℝ)^413 := by
    have hnat : (2020208043 : ℕ)^541*25000000000000^413 ≤ 3076517215787^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020208043 10000000000 3076517215787 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711981911/5000000000 : ℝ)^541 ≤ (2804492633229/6250000000000 : ℝ)^413 := by
    have hnat : (2711981911 : ℕ)^541*6250000000000^413 ≤ 2804492633229^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711981911 5000000000 2804492633229 6250000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233768611/10000000000 : ℝ)^541 ≤ (42822048988713/100000000000000 : ℝ)^413 := by
    have hnat : (5233768611 : ℕ)^541*100000000000000^413 ≤ 42822048988713^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233768611 10000000000 42822048988713 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020208043/10000000000 : ℝ), (2711981911/5000000000 : ℝ), (5233768611/10000000000 : ℝ)] ![(3076517215787/25000000000000 : ℝ), (2804492633229/6250000000000 : ℝ), (42822048988713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020208043/10000000000 : ℝ)|^541 ≤ (3076517215787/25000000000000 : ℝ)^413
        have hw : |(-2020208043/10000000000 : ℝ)|=(2020208043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711981911/5000000000 : ℝ)|^541 ≤ (2804492633229/6250000000000 : ℝ)^413
        have hw : |(2711981911/5000000000 : ℝ)|=(2711981911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233768611/10000000000 : ℝ)|^541 ≤ (42822048988713/100000000000000 : ℝ)^413
        have hw : |(5233768611/10000000000 : ℝ)|=(5233768611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5351759351/10000000000 : ℝ)*x 0 + (-2117350369/10000000000 : ℝ)*x 1 + (523376877/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351759351/10000000000 : ℝ)^541 ≤ (44091029259699/100000000000000 : ℝ)^413 := by
    have hnat : (5351759351 : ℕ)^541*100000000000000^413 ≤ 44091029259699^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351759351 10000000000 44091029259699 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117350369/10000000000 : ℝ)^541 ≤ (1308692003651/10000000000000 : ℝ)^413 := by
    have hnat : (2117350369 : ℕ)^541*10000000000000^413 ≤ 1308692003651^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117350369 10000000000 1308692003651 10000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523376877/1000000000 : ℝ)^541 ≤ (21411025346411/50000000000000 : ℝ)^413 := by
    have hnat : (523376877 : ℕ)^541*50000000000000^413 ≤ 21411025346411^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523376877 1000000000 21411025346411 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351759351/10000000000 : ℝ), (-2117350369/10000000000 : ℝ), (523376877/1000000000 : ℝ)] ![(44091029259699/100000000000000 : ℝ), (1308692003651/10000000000000 : ℝ), (21411025346411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351759351/10000000000 : ℝ)|^541 ≤ (44091029259699/100000000000000 : ℝ)^413
        have hw : |(5351759351/10000000000 : ℝ)|=(5351759351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117350369/10000000000 : ℝ)|^541 ≤ (1308692003651/10000000000000 : ℝ)^413
        have hw : |(-2117350369/10000000000 : ℝ)|=(2117350369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523376877/1000000000 : ℝ)|^541 ≤ (21411025346411/50000000000000 : ℝ)^413
        have hw : |(523376877/1000000000 : ℝ)|=(523376877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5351759323/10000000000 : ℝ)*x 0 + (2616884301/5000000000 : ℝ)*x 1 + (-2117350629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351759323/10000000000 : ℝ)^541 ≤ (11022757239381/25000000000000 : ℝ)^413 := by
    have hnat : (5351759323 : ℕ)^541*25000000000000^413 ≤ 11022757239381^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351759323 10000000000 11022757239381 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616884301/5000000000 : ℝ)^541 ≤ (21411024446127/50000000000000 : ℝ)^413 := by
    have hnat : (2616884301 : ℕ)^541*50000000000000^413 ≤ 21411024446127^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616884301 5000000000 21411024446127 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117350629/10000000000 : ℝ)^541 ≤ (6543461070787/50000000000000 : ℝ)^413 := by
    have hnat : (2117350629 : ℕ)^541*50000000000000^413 ≤ 6543461070787^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117350629 10000000000 6543461070787 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351759323/10000000000 : ℝ), (2616884301/5000000000 : ℝ), (-2117350629/10000000000 : ℝ)] ![(11022757239381/25000000000000 : ℝ), (21411024446127/50000000000000 : ℝ), (6543461070787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351759323/10000000000 : ℝ)|^541 ≤ (11022757239381/25000000000000 : ℝ)^413
        have hw : |(5351759323/10000000000 : ℝ)|=(5351759323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616884301/5000000000 : ℝ)|^541 ≤ (21411024446127/50000000000000 : ℝ)^413
        have hw : |(2616884301/5000000000 : ℝ)|=(2616884301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117350629/10000000000 : ℝ)|^541 ≤ (6543461070787/50000000000000 : ℝ)^413
        have hw : |(-2117350629/10000000000 : ℝ)|=(2117350629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1079737341/2500000000 : ℝ)*x 0 + (1030533753/2500000000 : ℝ)*x 1 + (4524412959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079737341/2500000000 : ℝ)^541 ≤ (33294447543927/100000000000000 : ℝ)^413 := by
    have hnat : (1079737341 : ℕ)^541*100000000000000^413 ≤ 33294447543927^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079737341 2500000000 33294447543927 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030533753/2500000000 : ℝ)^541 ≤ (15660587824883/50000000000000 : ℝ)^413 := by
    have hnat : (1030533753 : ℕ)^541*50000000000000^413 ≤ 15660587824883^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030533753 2500000000 15660587824883 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524412959/10000000000 : ℝ)^541 ≤ (442304709911/1250000000000 : ℝ)^413 := by
    have hnat : (4524412959 : ℕ)^541*1250000000000^413 ≤ 442304709911^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524412959 10000000000 442304709911 1250000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079737341/2500000000 : ℝ), (1030533753/2500000000 : ℝ), (4524412959/10000000000 : ℝ)] ![(33294447543927/100000000000000 : ℝ), (15660587824883/50000000000000 : ℝ), (442304709911/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079737341/2500000000 : ℝ)|^541 ≤ (33294447543927/100000000000000 : ℝ)^413
        have hw : |(1079737341/2500000000 : ℝ)|=(1079737341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030533753/2500000000 : ℝ)|^541 ≤ (15660587824883/50000000000000 : ℝ)^413
        have hw : |(1030533753/2500000000 : ℝ)|=(1030533753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524412959/10000000000 : ℝ)|^541 ≤ (442304709911/1250000000000 : ℝ)^413
        have hw : |(4524412959/10000000000 : ℝ)|=(4524412959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020226001/10000000000 : ℝ)*x 0 + (2617274887/5000000000 : ℝ)*x 1 + (1084635599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020226001/10000000000 : ℝ)^541 ≤ (3076553039371/25000000000000 : ℝ)^413 := by
    have hnat : (2020226001 : ℕ)^541*25000000000000^413 ≤ 3076553039371^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020226001 10000000000 3076553039371 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617274887/5000000000 : ℝ)^541 ≤ (42830421424939/100000000000000 : ℝ)^413 := by
    have hnat : (2617274887 : ℕ)^541*100000000000000^413 ≤ 42830421424939^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617274887 5000000000 42830421424939 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084635599/2000000000 : ℝ)^541 ≤ (8972673280223/20000000000000 : ℝ)^413 := by
    have hnat : (1084635599 : ℕ)^541*20000000000000^413 ≤ 8972673280223^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084635599 2000000000 8972673280223 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020226001/10000000000 : ℝ), (2617274887/5000000000 : ℝ), (1084635599/2000000000 : ℝ)] ![(3076553039371/25000000000000 : ℝ), (42830421424939/100000000000000 : ℝ), (8972673280223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020226001/10000000000 : ℝ)|^541 ≤ (3076553039371/25000000000000 : ℝ)^413
        have hw : |(-2020226001/10000000000 : ℝ)|=(2020226001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617274887/5000000000 : ℝ)|^541 ≤ (42830421424939/100000000000000 : ℝ)^413
        have hw : |(2617274887/5000000000 : ℝ)|=(2617274887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084635599/2000000000 : ℝ)|^541 ≤ (8972673280223/20000000000000 : ℝ)^413
        have hw : |(1084635599/2000000000 : ℝ)|=(1084635599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651312753/5000000000 : ℝ)*x 0 + (-1927941017/10000000000 : ℝ)*x 1 + (677897249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651312753/5000000000 : ℝ)^541 ≤ (21780767045469/50000000000000 : ℝ)^413 := by
    have hnat : (2651312753 : ℕ)^541*50000000000000^413 ≤ 21780767045469^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651312753 5000000000 21780767045469 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927941017/10000000000 : ℝ)^541 ≤ (11575099519413/100000000000000 : ℝ)^413 := by
    have hnat : (1927941017 : ℕ)^541*100000000000000^413 ≤ 11575099519413^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927941017 10000000000 11575099519413 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677897249/1250000000 : ℝ)^541 ≤ (22431683184303/50000000000000 : ℝ)^413 := by
    have hnat : (677897249 : ℕ)^541*50000000000000^413 ≤ 22431683184303^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677897249 1250000000 22431683184303 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651312753/5000000000 : ℝ), (-1927941017/10000000000 : ℝ), (677897249/1250000000 : ℝ)] ![(21780767045469/50000000000000 : ℝ), (11575099519413/100000000000000 : ℝ), (22431683184303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651312753/5000000000 : ℝ)|^541 ≤ (21780767045469/50000000000000 : ℝ)^413
        have hw : |(2651312753/5000000000 : ℝ)|=(2651312753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927941017/10000000000 : ℝ)|^541 ≤ (11575099519413/100000000000000 : ℝ)^413
        have hw : |(-1927941017/10000000000 : ℝ)|=(1927941017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677897249/1250000000 : ℝ)|^541 ≤ (22431683184303/50000000000000 : ℝ)^413
        have hw : |(677897249/1250000000 : ℝ)|=(677897249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1060525083/2000000000 : ℝ)*x 0 + (5423178061/10000000000 : ℝ)*x 1 + (-1927941047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060525083/2000000000 : ℝ)^541 ≤ (5445191638959/12500000000000 : ℝ)^413 := by
    have hnat : (1060525083 : ℕ)^541*12500000000000^413 ≤ 5445191638959^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060525083 2000000000 5445191638959 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423178061/10000000000 : ℝ)^541 ≤ (22431683558159/50000000000000 : ℝ)^413 := by
    have hnat : (5423178061 : ℕ)^541*50000000000000^413 ≤ 22431683558159^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423178061 10000000000 22431683558159 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1927941047/10000000000 : ℝ)^541 ≤ (1446887469419/12500000000000 : ℝ)^413 := by
    have hnat : (1927941047 : ℕ)^541*12500000000000^413 ≤ 1446887469419^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927941047 10000000000 1446887469419 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060525083/2000000000 : ℝ), (5423178061/10000000000 : ℝ), (-1927941047/10000000000 : ℝ)] ![(5445191638959/12500000000000 : ℝ), (22431683558159/50000000000000 : ℝ), (1446887469419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060525083/2000000000 : ℝ)|^541 ≤ (5445191638959/12500000000000 : ℝ)^413
        have hw : |(1060525083/2000000000 : ℝ)|=(1060525083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423178061/10000000000 : ℝ)|^541 ≤ (22431683558159/50000000000000 : ℝ)^413
        have hw : |(5423178061/10000000000 : ℝ)|=(5423178061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1927941047/10000000000 : ℝ)|^541 ≤ (1446887469419/12500000000000 : ℝ)^413
        have hw : |(-1927941047/10000000000 : ℝ)|=(1927941047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s3_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1079746771/2500000000 : ℝ)*x 0 + (180910433/400000000 : ℝ)*x 1 + (4123797051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079746771/2500000000 : ℝ)^541 ≤ (8323707111467/25000000000000 : ℝ)^413 := by
    have hnat : (1079746771 : ℕ)^541*25000000000000^413 ≤ 8323707111467^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079746771 2500000000 8323707111467 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180910433/400000000 : ℝ)^541 ≤ (35367452239473/100000000000000 : ℝ)^413 := by
    have hnat : (180910433 : ℕ)^541*100000000000000^413 ≤ 35367452239473^413*400000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180910433 400000000 35367452239473 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4123797051/10000000000 : ℝ)^541 ≤ (15668859651123/50000000000000 : ℝ)^413 := by
    have hnat : (4123797051 : ℕ)^541*50000000000000^413 ≤ 15668859651123^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123797051 10000000000 15668859651123 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079746771/2500000000 : ℝ), (180910433/400000000 : ℝ), (4123797051/10000000000 : ℝ)] ![(8323707111467/25000000000000 : ℝ), (35367452239473/100000000000000 : ℝ), (15668859651123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079746771/2500000000 : ℝ)|^541 ≤ (8323707111467/25000000000000 : ℝ)^413
        have hw : |(1079746771/2500000000 : ℝ)|=(1079746771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180910433/400000000 : ℝ)|^541 ≤ (35367452239473/100000000000000 : ℝ)^413
        have hw : |(180910433/400000000 : ℝ)|=(180910433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4123797051/10000000000 : ℝ)|^541 ≤ (15668859651123/50000000000000 : ℝ)^413
        have hw : |(4123797051/10000000000 : ℝ)|=(4123797051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3201/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3201/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3201/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3201/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3201/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3201/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10017/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (2995719668215917/50000000000000000000 : ℝ) := by
    have hpowers : (10017/100000 : ℝ)^4327 ≤ (2995719668215917/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10017 : ℕ)^4327*50000000000000000000^1024 ≤ 2995719668215917^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10017 100000 2995719668215917 50000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10017/100000 : ℝ)) (X := (2995719668215917/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3201/20000 : ℝ) ^ (4327/1024 : ℝ) ≤ (43402423985763209/100000000000000000000 : ℝ) := by
    have hpowers : (3201/20000 : ℝ)^4327 ≤ (43402423985763209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3201 : ℕ)^4327*100000000000000000000^1024 ≤ 43402423985763209^1024*20000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3201 20000 43402423985763209 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3201/20000 : ℝ)) (X := (43402423985763209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002995719668215917/25000000000000000000 : ℝ) ≤ (10000283566133703/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (25002995719668215917/25000000000000000000 : ℝ)^1024 ≤ (10000283566133703/10000000000000000 : ℝ)^4327 := by
      have hnat : (25002995719668215917 : ℕ)^1024*10000000000000000^4327 ≤ 10000283566133703^4327*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002995719668215917 25000000000000000000 10000283566133703 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283566133703/10000000000000000 : ℝ)) (X := (25002995719668215917/25000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049393863322195043/100000000000000000000 : ℝ) ≤ (10001168703106947/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (100049393863322195043/100000000000000000000 : ℝ)^1024 ≤ (10001168703106947/10000000000000000 : ℝ)^4327 := by
      have hnat : (100049393863322195043 : ℕ)^1024*10000000000000000^4327 ≤ 10001168703106947^4327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049393863322195043 100000000000000000000 10001168703106947 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001168703106947/10000000000000000 : ℝ)) (X := (100049393863322195043/100000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043402423985763209/50000000000000000000 : ℝ) ≤ (10002053840080191/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50043402423985763209/50000000000000000000 : ℝ)^1024 ≤ (10002053840080191/10000000000000000 : ℝ)^4327 := by
      have hnat : (50043402423985763209 : ℕ)^1024*10000000000000000^4327 ≤ 10002053840080191^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043402423985763209 50000000000000000000 10002053840080191 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002053840080191/10000000000000000 : ℝ)) (X := (50043402423985763209/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2995719668215917/50000000000000000000 : ℝ) ≤ ((4988663763323886939/4990000000000000000 : ℝ)+2*(73761414437/49900000000000 : ℝ)*(10017/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (4988663763323886939/4990000000000000000 : ℝ)+2*(73761414437/49900000000000 : ℝ)*(10017/100000 : ℝ)=(10000283566133703/10000000000000000 : ℝ) by norm_num, show 1+2*(2995719668215917/50000000000000000000 : ℝ)=(25002995719668215917/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43402423985763209/100000000000000000000 : ℝ)+(2995719668215917/50000000000000000000 : ℝ) ≤ ((4988663763323886939/4990000000000000000 : ℝ)+(73761414437/49900000000000 : ℝ)*((3201/20000 : ℝ)+(10017/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (4988663763323886939/4990000000000000000 : ℝ)+(73761414437/49900000000000 : ℝ)*((3201/20000 : ℝ)+(10017/100000 : ℝ))=(10001168703106947/10000000000000000 : ℝ) by norm_num, show 1+(43402423985763209/100000000000000000000 : ℝ)+(2995719668215917/50000000000000000000 : ℝ)=(100049393863322195043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43402423985763209/100000000000000000000 : ℝ) ≤ ((4988663763323886939/4990000000000000000 : ℝ)+2*(73761414437/49900000000000 : ℝ)*(3201/20000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (4988663763323886939/4990000000000000000 : ℝ)+2*(73761414437/49900000000000 : ℝ)*(3201/20000 : ℝ)=(10002053840080191/10000000000000000 : ℝ) by norm_num, show 1+2*(43402423985763209/100000000000000000000 : ℝ)=(50043402423985763209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4988663763323886939/4990000000000000000 : ℝ)*(X 1 0+X 2 0)+(73761414437/49900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (3201/20000 : ℝ)) (c := (4988663763323886939/4990000000000000000 : ℝ)) (alpha := (73761414437/49900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4988663763323886939/4990000000000000000 : ℝ)*(X 0 1+X 2 1)+(73761414437/49900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (3201/20000 : ℝ)) (c := (4988663763323886939/4990000000000000000 : ℝ)) (alpha := (73761414437/49900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4988663763323886939/4990000000000000000 : ℝ)*(X 0 2+X 1 2)+(73761414437/49900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (3201/20000 : ℝ)) (c := (4988663763323886939/4990000000000000000 : ℝ)) (alpha := (73761414437/49900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2020208043/10000000000 : ℝ)*X 0 0+(2711981911/5000000000 : ℝ)*X 0 1+(5233768611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351759351/10000000000 : ℝ)*X 1 0+(-2117350369/10000000000 : ℝ)*X 1 1+(523376877/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351759323/10000000000 : ℝ)*X 2 0+(2616884301/5000000000 : ℝ)*X 2 1+(-2117350629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079737341/2500000000 : ℝ)*X 0 0+(1030533753/2500000000 : ℝ)*X 0 1+(4524412959/10000000000 : ℝ)*X 0 2+(1079737341/2500000000 : ℝ)*X 1 0+(1030533753/2500000000 : ℝ)*X 1 1+(4524412959/10000000000 : ℝ)*X 1 2+(1079737341/2500000000 : ℝ)*X 2 0+(1030533753/2500000000 : ℝ)*X 2 1+(4524412959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2020226001/10000000000 : ℝ)*X 0 0+(2617274887/5000000000 : ℝ)*X 0 1+(1084635599/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651312753/5000000000 : ℝ)*X 1 0+(-1927941017/10000000000 : ℝ)*X 1 1+(677897249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060525083/2000000000 : ℝ)*X 2 0+(5423178061/10000000000 : ℝ)*X 2 1+(-1927941047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079746771/2500000000 : ℝ)*X 0 0+(180910433/400000000 : ℝ)*X 0 1+(4123797051/10000000000 : ℝ)*X 0 2+(1079746771/2500000000 : ℝ)*X 1 0+(180910433/400000000 : ℝ)*X 1 1+(4123797051/10000000000 : ℝ)*X 1 2+(1079746771/2500000000 : ℝ)*X 2 0+(180910433/400000000 : ℝ)*X 2 1+(4123797051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (819802367378910307756331547/124750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (956667377/100000000000000 : ℝ)*(base19) + (948560689/100000000000000 : ℝ)*(base23) + (52708909/100000000000000 : ℝ)*(lower2) + (275794887/100000000000000 : ℝ)*(upper3) + (63092223/100000000000000 : ℝ)*(lower4) + (1935913361471691/50000000000000 : ℝ)*(major0) + (1935913361471691/50000000000000 : ℝ)*(major1) + (1935913361471691/50000000000000 : ℝ)*(major2) + (5257779402558279/100000000000000 : ℝ)*(sp0) + (5257792372012911/100000000000000 : ℝ)*(sp1) + (5257792380119599/100000000000000 : ℝ)*(sp2) + (9710351273383/390625000000 : ℝ)*(sp3) + (13926122009/100000000000000 : ℝ)*(sp4) + (311630261/3125000000000 : ℝ)*(sp7) + (2485859898154399/100000000000000 : ℝ)*(f.failure) + (164306041521259/3125000000000 : ℝ)*(f.sum) + (1103458119237/311875000000000000000000000 : ℝ)*base66 + (2952078159530156151/249500000000000000000000000000000 : ℝ)*base68 + (1732651182966156151/249500000000000000000000000000000 : ℝ)*base70 + (487394479480343849/249500000000000000000000000000000 : ℝ)*base71 + (14526903092481/2495000000000000000000000000 : ℝ)*base74 + (3480702335943156151/249500000000000000000000000000000 : ℝ)*base76 + (1319154945838343849/249500000000000000000000000000000 : ℝ)*base77 + (3401445696883156151/249500000000000000000000000000000 : ℝ)*base80 + (17030733885501/2495000000000000000000000000 : ℝ)*base82 + (1246699/500000000000000000000 : ℝ)*base89 + (1246699/500000000000000000000 : ℝ)*base91 + (1246699/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689313363250195333252332867/62375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1986727391/100000000000000 : ℝ)*(base19) + (1029409181/50000000000000 : ℝ)*(base23) + (109862397/50000000000000 : ℝ)*(upper3) + (10090551/12500000000000 : ℝ)*(lower4) + (47560323/20000000000000 : ℝ)*(upper5) + (975990580926349/25000000000000 : ℝ)*(major0) + (975990580926349/25000000000000 : ℝ)*(major1) + (975990580926349/25000000000000 : ℝ)*(major2) + (9080531237/25000000000000 : ℝ)*(sp1) + (37491484291/100000000000000 : ℝ)*(sp2) + (5301432103939153/100000000000000 : ℝ)*(sp4) + (5301393795086813/100000000000000 : ℝ)*(sp5) + (5301392553636499/100000000000000 : ℝ)*(sp6) + (313311521887637/12500000000000 : ℝ)*(sp7) + (313311521887637/12500000000000 : ℝ)*(f.failure) + (5301432103939153/100000000000000 : ℝ)*(f.sum) + (1207439440893/2495000000000000000000000000 : ℝ)*base66 + (438116447668855711/124750000000000000000000000000000 : ℝ)*base67 + (174910105828894289/124750000000000000000000000000000 : ℝ)*base70 + (648517356560855711/124750000000000000000000000000000 : ℝ)*base71 + (5211640032387/2495000000000000000000000000 : ℝ)*base73 + (2631621180351355711/124750000000000000000000000000000 : ℝ)*base75 + (223344918451144289/124750000000000000000000000000000 : ℝ)*base78 + (2445122117343605711/124750000000000000000000000000000 : ℝ)*base79 + (1858132898241/311875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (52537/62500000000000000000 : ℝ)*base89 + (52537/62500000000000000000 : ℝ)*base91 + (52537/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_s4_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010736543/5000000000 : ℝ)*x 0 + (5413495733/10000000000 : ℝ)*x 1 + (5243405307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010736543/5000000000 : ℝ)^541 ≤ (1231616413181/10000000000000 : ℝ)^413 := by
    have hnat : (1010736543 : ℕ)^541*10000000000000^413 ≤ 1231616413181^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010736543 5000000000 1231616413181 10000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413495733/10000000000 : ℝ)^541 ≤ (8951694906423/20000000000000 : ℝ)^413 := by
    have hnat : (5413495733 : ℕ)^541*20000000000000^413 ≤ 8951694906423^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413495733 10000000000 8951694906423 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243405307/10000000000 : ℝ)^541 ≤ (1717014452633/4000000000000 : ℝ)^413 := by
    have hnat : (5243405307 : ℕ)^541*4000000000000^413 ≤ 1717014452633^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243405307 10000000000 1717014452633 4000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010736543/5000000000 : ℝ), (5413495733/10000000000 : ℝ), (5243405307/10000000000 : ℝ)] ![(1231616413181/10000000000000 : ℝ), (8951694906423/20000000000000 : ℝ), (1717014452633/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010736543/5000000000 : ℝ)|^541 ≤ (1231616413181/10000000000000 : ℝ)^413
        have hw : |(-1010736543/5000000000 : ℝ)|=(1010736543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413495733/10000000000 : ℝ)|^541 ≤ (8951694906423/20000000000000 : ℝ)^413
        have hw : |(5413495733/10000000000 : ℝ)|=(5413495733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243405307/10000000000 : ℝ)|^541 ≤ (1717014452633/4000000000000 : ℝ)^413
        have hw : |(5243405307/10000000000 : ℝ)|=(5243405307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (534908093/1000000000 : ℝ)*x 0 + (-1054076841/5000000000 : ℝ)*x 1 + (5243405537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534908093/1000000000 : ℝ)^541 ≤ (11015531513257/25000000000000 : ℝ)^413 := by
    have hnat : (534908093 : ℕ)^541*25000000000000^413 ≤ 11015531513257^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534908093 1000000000 11015531513257 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054076841/5000000000 : ℝ)^541 ≤ (6506255075883/50000000000000 : ℝ)^413 := by
    have hnat : (1054076841 : ℕ)^541*50000000000000^413 ≤ 6506255075883^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054076841 5000000000 6506255075883 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243405537/10000000000 : ℝ)^541 ≤ (42925363782293/100000000000000 : ℝ)^413 := by
    have hnat : (5243405537 : ℕ)^541*100000000000000^413 ≤ 42925363782293^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243405537 10000000000 42925363782293 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534908093/1000000000 : ℝ), (-1054076841/5000000000 : ℝ), (5243405537/10000000000 : ℝ)] ![(11015531513257/25000000000000 : ℝ), (6506255075883/50000000000000 : ℝ), (42925363782293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534908093/1000000000 : ℝ)|^541 ≤ (11015531513257/25000000000000 : ℝ)^413
        have hw : |(534908093/1000000000 : ℝ)|=(534908093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054076841/5000000000 : ℝ)|^541 ≤ (6506255075883/50000000000000 : ℝ)^413
        have hw : |(-1054076841/5000000000 : ℝ)|=(1054076841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243405537/10000000000 : ℝ)|^541 ≤ (42925363782293/100000000000000 : ℝ)^413
        have hw : |(5243405537/10000000000 : ℝ)|=(5243405537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349080907/10000000000 : ℝ)*x 0 + (2621702637/5000000000 : ℝ)*x 1 + (-2108154061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349080907/10000000000 : ℝ)^541 ≤ (11015531451213/25000000000000 : ℝ)^413 := by
    have hnat : (5349080907 : ℕ)^541*25000000000000^413 ≤ 11015531451213^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349080907 10000000000 11015531451213 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621702637/5000000000 : ℝ)^541 ≤ (2146268048097/5000000000000 : ℝ)^413 := by
    have hnat : (2621702637 : ℕ)^541*5000000000000^413 ≤ 2146268048097^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621702637 5000000000 2146268048097 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108154061/10000000000 : ℝ)^541 ≤ (3253128304041/25000000000000 : ℝ)^413 := by
    have hnat : (2108154061 : ℕ)^541*25000000000000^413 ≤ 3253128304041^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108154061 10000000000 3253128304041 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349080907/10000000000 : ℝ), (2621702637/5000000000 : ℝ), (-2108154061/10000000000 : ℝ)] ![(11015531451213/25000000000000 : ℝ), (2146268048097/5000000000000 : ℝ), (3253128304041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349080907/10000000000 : ℝ)|^541 ≤ (11015531451213/25000000000000 : ℝ)^413
        have hw : |(5349080907/10000000000 : ℝ)|=(5349080907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621702637/5000000000 : ℝ)|^541 ≤ (2146268048097/5000000000000 : ℝ)^413
        have hw : |(2621702637/5000000000 : ℝ)|=(2621702637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108154061/10000000000 : ℝ)|^541 ≤ (3253128304041/25000000000000 : ℝ)^413
        have hw : |(-2108154061/10000000000 : ℝ)|=(2108154061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (431972017/1000000000 : ℝ)*x 0 + (4143301479/10000000000 : ℝ)*x 1 + (4503056827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431972017/1000000000 : ℝ)^541 ≤ (16651115728803/50000000000000 : ℝ)^413 := by
    have hnat : (431972017 : ℕ)^541*50000000000000^413 ≤ 16651115728803^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431972017 1000000000 16651115728803 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4143301479/10000000000 : ℝ)^541 ≤ (1576600866277/5000000000000 : ℝ)^413 := by
    have hnat : (4143301479 : ℕ)^541*5000000000000^413 ≤ 1576600866277^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143301479 10000000000 1576600866277 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503056827/10000000000 : ℝ)^541 ≤ (35165751203933/100000000000000 : ℝ)^413 := by
    have hnat : (4503056827 : ℕ)^541*100000000000000^413 ≤ 35165751203933^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503056827 10000000000 35165751203933 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431972017/1000000000 : ℝ), (4143301479/10000000000 : ℝ), (4503056827/10000000000 : ℝ)] ![(16651115728803/50000000000000 : ℝ), (1576600866277/5000000000000 : ℝ), (35165751203933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431972017/1000000000 : ℝ)|^541 ≤ (16651115728803/50000000000000 : ℝ)^413
        have hw : |(431972017/1000000000 : ℝ)|=(431972017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4143301479/10000000000 : ℝ)|^541 ≤ (1576600866277/5000000000000 : ℝ)^413
        have hw : |(4143301479/10000000000 : ℝ)|=(4143301479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503056827/10000000000 : ℝ)|^541 ≤ (35165751203933/100000000000000 : ℝ)^413
        have hw : |(4503056827/10000000000 : ℝ)|=(4503056827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-505371439/2500000000 : ℝ)*x 0 + (81937977/156250000 : ℝ)*x 1 + (5412867309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505371439/2500000000 : ℝ)^541 ≤ (492650610023/4000000000000 : ℝ)^413 := by
    have hnat : (505371439 : ℕ)^541*4000000000000^413 ≤ 492650610023^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505371439 2500000000 492650610023 4000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81937977/156250000 : ℝ)^541 ≤ (5366508271227/12500000000000 : ℝ)^413 := by
    have hnat : (81937977 : ℕ)^541*12500000000000^413 ≤ 5366508271227^413*156250000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81937977 156250000 5366508271227 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412867309/10000000000 : ℝ)^541 ≤ (22375834284109/50000000000000 : ℝ)^413 := by
    have hnat : (5412867309 : ℕ)^541*50000000000000^413 ≤ 22375834284109^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412867309 10000000000 22375834284109 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505371439/2500000000 : ℝ), (81937977/156250000 : ℝ), (5412867309/10000000000 : ℝ)] ![(492650610023/4000000000000 : ℝ), (5366508271227/12500000000000 : ℝ), (22375834284109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505371439/2500000000 : ℝ)|^541 ≤ (492650610023/4000000000000 : ℝ)^413
        have hw : |(-505371439/2500000000 : ℝ)|=(505371439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81937977/156250000 : ℝ)|^541 ≤ (5366508271227/12500000000000 : ℝ)^413
        have hw : |(81937977/156250000 : ℝ)|=(81937977/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412867309/10000000000 : ℝ)|^541 ≤ (22375834284109/50000000000000 : ℝ)^413
        have hw : |(5412867309/10000000000 : ℝ)|=(5412867309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305141117/10000000000 : ℝ)*x 0 + (-1938691921/10000000000 : ℝ)*x 1 + (1082573463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305141117/10000000000 : ℝ)^541 ≤ (43588606994161/100000000000000 : ℝ)^413 := by
    have hnat : (5305141117 : ℕ)^541*100000000000000^413 ≤ 43588606994161^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305141117 10000000000 43588606994161 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938691921/10000000000 : ℝ)^541 ≤ (182183193037/1562500000000 : ℝ)^413 := by
    have hnat : (1938691921 : ℕ)^541*1562500000000^413 ≤ 182183193037^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938691921 10000000000 182183193037 1562500000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082573463/2000000000 : ℝ)^541 ≤ (22375834316599/50000000000000 : ℝ)^413 := by
    have hnat : (1082573463 : ℕ)^541*50000000000000^413 ≤ 22375834316599^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082573463 2000000000 22375834316599 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305141117/10000000000 : ℝ), (-1938691921/10000000000 : ℝ), (1082573463/2000000000 : ℝ)] ![(43588606994161/100000000000000 : ℝ), (182183193037/1562500000000 : ℝ), (22375834316599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305141117/10000000000 : ℝ)|^541 ≤ (43588606994161/100000000000000 : ℝ)^413
        have hw : |(5305141117/10000000000 : ℝ)|=(5305141117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938691921/10000000000 : ℝ)|^541 ≤ (182183193037/1562500000000 : ℝ)^413
        have hw : |(-1938691921/10000000000 : ℝ)|=(1938691921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082573463/2000000000 : ℝ)|^541 ≤ (22375834316599/50000000000000 : ℝ)^413
        have hw : |(1082573463/2000000000 : ℝ)|=(1082573463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663142641/1250000000 : ℝ)*x 0 + (1353216827/2500000000 : ℝ)*x 1 + (-387738383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663142641/1250000000 : ℝ)^541 ≤ (43588607112551/100000000000000 : ℝ)^413 := by
    have hnat : (663142641 : ℕ)^541*100000000000000^413 ≤ 43588607112551^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663142641 1250000000 43588607112551 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353216827/2500000000 : ℝ)^541 ≤ (11187917139347/25000000000000 : ℝ)^413 := by
    have hnat : (1353216827 : ℕ)^541*25000000000000^413 ≤ 11187917139347^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353216827 2500000000 11187917139347 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387738383/2000000000 : ℝ)^541 ≤ (11659724307099/100000000000000 : ℝ)^413 := by
    have hnat : (387738383 : ℕ)^541*100000000000000^413 ≤ 11659724307099^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387738383 2000000000 11659724307099 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663142641/1250000000 : ℝ), (1353216827/2500000000 : ℝ), (-387738383/2000000000 : ℝ)] ![(43588607112551/100000000000000 : ℝ), (11187917139347/25000000000000 : ℝ), (11659724307099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663142641/1250000000 : ℝ)|^541 ≤ (43588607112551/100000000000000 : ℝ)^413
        have hw : |(663142641/1250000000 : ℝ)|=(663142641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353216827/2500000000 : ℝ)|^541 ≤ (11187917139347/25000000000000 : ℝ)^413
        have hw : |(1353216827/2500000000 : ℝ)|=(1353216827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387738383/2000000000 : ℝ)|^541 ≤ (11659724307099/100000000000000 : ℝ)^413
        have hw : |(-387738383/2000000000 : ℝ)|=(387738383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s4_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4319746823/10000000000 : ℝ)*x 0 + (4501734569/10000000000 : ℝ)*x 1 + (165785247/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319746823/10000000000 : ℝ)^541 ≤ (16651250309091/50000000000000 : ℝ)^413 := by
    have hnat : (4319746823 : ℕ)^541*50000000000000^413 ≤ 16651250309091^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319746823 10000000000 16651250309091 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501734569/10000000000 : ℝ)^541 ≤ (8788056404213/25000000000000 : ℝ)^413 := by
    have hnat : (4501734569 : ℕ)^541*25000000000000^413 ≤ 8788056404213^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501734569 10000000000 8788056404213 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165785247/400000000 : ℝ)^541 ≤ (15772636874879/50000000000000 : ℝ)^413 := by
    have hnat : (165785247 : ℕ)^541*50000000000000^413 ≤ 15772636874879^413*400000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165785247 400000000 15772636874879 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319746823/10000000000 : ℝ), (4501734569/10000000000 : ℝ), (165785247/400000000 : ℝ)] ![(16651250309091/50000000000000 : ℝ), (8788056404213/25000000000000 : ℝ), (15772636874879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319746823/10000000000 : ℝ)|^541 ≤ (16651250309091/50000000000000 : ℝ)^413
        have hw : |(4319746823/10000000000 : ℝ)|=(4319746823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501734569/10000000000 : ℝ)|^541 ≤ (8788056404213/25000000000000 : ℝ)^413
        have hw : |(4501734569/10000000000 : ℝ)|=(4501734569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165785247/400000000 : ℝ)|^541 ≤ (15772636874879/50000000000000 : ℝ)^413
        have hw : |(165785247/400000000 : ℝ)|=(165785247/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14987/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (10961/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (8766059481545829/100000000000000000000 : ℝ) := by
    have hpowers : (10961/100000 : ℝ)^4327 ≤ (8766059481545829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10961 : ℕ)^4327*100000000000000000000^1024 ≤ 8766059481545829^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10961 100000 8766059481545829 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10961/100000 : ℝ)) (X := (8766059481545829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14987/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (32878474487540631/100000000000000000000 : ℝ) := by
    have hpowers : (14987/100000 : ℝ)^4327 ≤ (32878474487540631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14987 : ℕ)^4327*100000000000000000000^1024 ≤ 32878474487540631^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14987 100000 32878474487540631 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14987/100000 : ℝ)) (X := (32878474487540631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008766059481545829/50000000000000000000 : ℝ) ≤ (312512964877959/312500000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50008766059481545829/50000000000000000000 : ℝ)^1024 ≤ (312512964877959/312500000000000 : ℝ)^4327 := by
      have hnat : (50008766059481545829 : ℕ)^1024*312500000000000^4327 ≤ 312512964877959^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008766059481545829 50000000000000000000 312512964877959 312500000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312512964877959/312500000000000 : ℝ)) (X := (50008766059481545829/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002082226698454323/5000000000000000000 : ℝ) ≤ (50004926880789/50000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (5002082226698454323/5000000000000000000 : ℝ)^1024 ≤ (50004926880789/50000000000000 : ℝ)^4327 := by
      have hnat : (5002082226698454323 : ℕ)^1024*50000000000000^4327 ≤ 50004926880789^4327*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002082226698454323 5000000000000000000 50004926880789 50000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50004926880789/50000000000000 : ℝ)) (X := (5002082226698454323/5000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032878474487540631/50000000000000000000 : ℝ) ≤ (625097242263807/625000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50032878474487540631/50000000000000000000 : ℝ)^1024 ≤ (625097242263807/625000000000000 : ℝ)^4327 := by
      have hnat : (50032878474487540631 : ℕ)^1024*625000000000000^4327 ≤ 625097242263807^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032878474487540631 50000000000000000000 625097242263807 625000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625097242263807/625000000000000 : ℝ)) (X := (50032878474487540631/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8766059481545829/100000000000000000000 : ℝ) ≤ ((838524245599451513/838750000000000000 : ℝ)+2*(23770835963/16775000000000 : ℝ)*(10961/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (838524245599451513/838750000000000000 : ℝ)+2*(23770835963/16775000000000 : ℝ)*(10961/100000 : ℝ)=(312512964877959/312500000000000 : ℝ) by norm_num, show 1+2*(8766059481545829/100000000000000000000 : ℝ)=(50008766059481545829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32878474487540631/100000000000000000000 : ℝ)+(8766059481545829/100000000000000000000 : ℝ) ≤ ((838524245599451513/838750000000000000 : ℝ)+(23770835963/16775000000000 : ℝ)*((14987/100000 : ℝ)+(10961/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (838524245599451513/838750000000000000 : ℝ)+(23770835963/16775000000000 : ℝ)*((14987/100000 : ℝ)+(10961/100000 : ℝ))=(50004926880789/50000000000000 : ℝ) by norm_num, show 1+(32878474487540631/100000000000000000000 : ℝ)+(8766059481545829/100000000000000000000 : ℝ)=(5002082226698454323/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32878474487540631/100000000000000000000 : ℝ) ≤ ((838524245599451513/838750000000000000 : ℝ)+2*(23770835963/16775000000000 : ℝ)*(14987/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (838524245599451513/838750000000000000 : ℝ)+2*(23770835963/16775000000000 : ℝ)*(14987/100000 : ℝ)=(625097242263807/625000000000000 : ℝ) by norm_num, show 1+2*(32878474487540631/100000000000000000000 : ℝ)=(50032878474487540631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (838524245599451513/838750000000000000 : ℝ)*(X 1 0+X 2 0)+(23770835963/16775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (838524245599451513/838750000000000000 : ℝ)) (alpha := (23770835963/16775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (838524245599451513/838750000000000000 : ℝ)*(X 0 1+X 2 1)+(23770835963/16775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (838524245599451513/838750000000000000 : ℝ)) (alpha := (23770835963/16775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (838524245599451513/838750000000000000 : ℝ)*(X 0 2+X 1 2)+(23770835963/16775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (14987/100000 : ℝ)) (c := (838524245599451513/838750000000000000 : ℝ)) (alpha := (23770835963/16775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1010736543/5000000000 : ℝ)*X 0 0+(5413495733/10000000000 : ℝ)*X 0 1+(5243405307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534908093/1000000000 : ℝ)*X 1 0+(-1054076841/5000000000 : ℝ)*X 1 1+(5243405537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349080907/10000000000 : ℝ)*X 2 0+(2621702637/5000000000 : ℝ)*X 2 1+(-2108154061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431972017/1000000000 : ℝ)*X 0 0+(4143301479/10000000000 : ℝ)*X 0 1+(4503056827/10000000000 : ℝ)*X 0 2+(431972017/1000000000 : ℝ)*X 1 0+(4143301479/10000000000 : ℝ)*X 1 1+(4503056827/10000000000 : ℝ)*X 1 2+(431972017/1000000000 : ℝ)*X 2 0+(4143301479/10000000000 : ℝ)*X 2 1+(4503056827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505371439/2500000000 : ℝ)*X 0 0+(81937977/156250000 : ℝ)*X 0 1+(5412867309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305141117/10000000000 : ℝ)*X 1 0+(-1938691921/10000000000 : ℝ)*X 1 1+(1082573463/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663142641/1250000000 : ℝ)*X 2 0+(1353216827/2500000000 : ℝ)*X 2 1+(-387738383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319746823/10000000000 : ℝ)*X 0 0+(4501734569/10000000000 : ℝ)*X 0 1+(165785247/400000000 : ℝ)*X 0 2+(4319746823/10000000000 : ℝ)*X 1 0+(4501734569/10000000000 : ℝ)*X 1 1+(165785247/400000000 : ℝ)*X 1 2+(4319746823/10000000000 : ℝ)*X 2 0+(4501734569/10000000000 : ℝ)*X 2 1+(165785247/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12902136280245195593230959/4193750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (172809603/20000000000000 : ℝ)*(base19) + (473293319/50000000000000 : ℝ)*(base23) + (171031919/50000000000000 : ℝ)*(upper3) + (249793/400000000000 : ℝ)*(lower4) + (865895247468969/20000000000000 : ℝ)*(major0) + (865895247468969/20000000000000 : ℝ)*(major1) + (865895247468969/20000000000000 : ℝ)*(major2) + (5879252046510311/100000000000000 : ℝ)*(sp0) + (1469815807379763/25000000000000 : ℝ)*(sp1) + (9406819296291/160000000000 : ℝ)*(sp2) + (694918835197503/25000000000000 : ℝ)*(sp3) + (12047056757/100000000000000 : ℝ)*(sp4) + (543399277/50000000000000 : ℝ)*(sp6) + (1617222761/12500000000000 : ℝ)*(sp7) + (27796882785721/1000000000000 : ℝ)*(f.failure) + (1469816023391767/25000000000000 : ℝ)*(f.sum) + (363269456129/335500000000000000000000000 : ℝ)*base66 + (3204714978156827/1525000000000000000000000000000 : ℝ)*base67 + (20734324269781827/1525000000000000000000000000000 : ℝ)*base69 + (9191122997968173/1525000000000000000000000000000 : ℝ)*base72 + (41135585991/20968750000000000000000000 : ℝ)*base73 + (14720771130431827/1525000000000000000000000000000 : ℝ)*base75 + (13590224957106827/1525000000000000000000000000000 : ℝ)*base77 + (3651843875581827/1525000000000000000000000000000 : ℝ)*base79 + (1709281932419/671000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (32579/5000000000000000000 : ℝ)*base90 + (32579/5000000000000000000 : ℝ)*base92 + (32579/5000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361760074926466425957553077/41937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11598573/781250000000 : ℝ)*(base19) + (1631925361/100000000000000 : ℝ)*(base23) + (181381447/100000000000000 : ℝ)*(upper3) + (59509957/100000000000000 : ℝ)*(lower4) + (88042219/50000000000000 : ℝ)*(upper5) + (4361594094413857/100000000000000 : ℝ)*(major0) + (4361594094413857/100000000000000 : ℝ)*(major1) + (4361594094413857/100000000000000 : ℝ)*(major2) + (5938636549/20000000000000 : ℝ)*(sp1) + (32452404473/100000000000000 : ℝ)*(sp2) + (148071968447377/2500000000000 : ℝ)*(sp4) + (5922847560094991/100000000000000 : ℝ)*(sp5) + (2961422326782623/50000000000000 : ℝ)*(sp6) + (700077290848393/25000000000000 : ℝ)*(sp7) + (700077290848393/25000000000000 : ℝ)*(f.failure) + (148071968447377/2500000000000 : ℝ)*(f.sum) + (275314302977/419375000000000000000000000 : ℝ)*base66 + (18336850226557669/7625000000000000000000000000000 : ℝ)*base68 + (102443499669442331/7625000000000000000000000000000 : ℝ)*base69 + (96288192419682669/7625000000000000000000000000000 : ℝ)*base72 + (3478291044379/3355000000000000000000000000 : ℝ)*base73 + (76815581030692331/7625000000000000000000000000000 : ℝ)*base75 + (28095865227567331/7625000000000000000000000000000 : ℝ)*base77 + (31631558032192331/7625000000000000000000000000000 : ℝ)*base79 + (5852636599571/3355000000000000000000000000 : ℝ)*base82 + (235507/125000000000000000000 : ℝ)*base90 + (235507/125000000000000000000 : ℝ)*base92 + (235507/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1368_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_s5_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-505420561/2500000000 : ℝ)*x 0 + (1082334911/2000000000 : ℝ)*x 1 + (4196071/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505420561/2500000000 : ℝ)^541 ≤ (6158916719303/50000000000000 : ℝ)^413 := by
    have hnat : (505420561 : ℕ)^541*50000000000000^413 ≤ 6158916719303^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505420561 2500000000 6158916719303 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082334911/2000000000 : ℝ)^541 ≤ (5592343933177/12500000000000 : ℝ)^413 := by
    have hnat : (1082334911 : ℕ)^541*12500000000000^413 ≤ 5592343933177^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082334911 2000000000 5592343933177 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4196071/8000000 : ℝ)^541 ≤ (21471707539991/50000000000000 : ℝ)^413 := by
    have hnat : (4196071 : ℕ)^541*50000000000000^413 ≤ 21471707539991^413*8000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196071 8000000 21471707539991 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505420561/2500000000 : ℝ), (1082334911/2000000000 : ℝ), (4196071/8000000 : ℝ)] ![(6158916719303/50000000000000 : ℝ), (5592343933177/12500000000000 : ℝ), (21471707539991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505420561/2500000000 : ℝ)|^541 ≤ (6158916719303/50000000000000 : ℝ)^413
        have hw : |(-505420561/2500000000 : ℝ)|=(505420561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082334911/2000000000 : ℝ)|^541 ≤ (5592343933177/12500000000000 : ℝ)^413
        have hw : |(1082334911/2000000000 : ℝ)|=(1082334911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4196071/8000000 : ℝ)|^541 ≤ (21471707539991/50000000000000 : ℝ)^413
        have hw : |(4196071/8000000 : ℝ)|=(4196071/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348613873/10000000000 : ℝ)*x 0 + (-84261771/400000000 : ℝ)*x 1 + (2622544357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348613873/10000000000 : ℝ)^541 ≤ (5507135804547/12500000000000 : ℝ)^413 := by
    have hnat : (5348613873 : ℕ)^541*12500000000000^413 ≤ 5507135804547^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348613873 10000000000 5507135804547 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84261771/400000000 : ℝ)^541 ≤ (6499749428387/50000000000000 : ℝ)^413 := by
    have hnat : (84261771 : ℕ)^541*50000000000000^413 ≤ 6499749428387^413*400000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84261771 400000000 6499749428387 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622544357/5000000000 : ℝ)^541 ≤ (10484232103/24414062500 : ℝ)^413 := by
    have hnat : (2622544357 : ℕ)^541*24414062500^413 ≤ 10484232103^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622544357 5000000000 10484232103 24414062500 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348613873/10000000000 : ℝ), (-84261771/400000000 : ℝ), (2622544357/5000000000 : ℝ)] ![(5507135804547/12500000000000 : ℝ), (6499749428387/50000000000000 : ℝ), (10484232103/24414062500 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348613873/10000000000 : ℝ)|^541 ≤ (5507135804547/12500000000000 : ℝ)^413
        have hw : |(5348613873/10000000000 : ℝ)|=(5348613873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84261771/400000000 : ℝ)|^541 ≤ (6499749428387/50000000000000 : ℝ)^413
        have hw : |(-84261771/400000000 : ℝ)|=(84261771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622544357/5000000000 : ℝ)|^541 ≤ (10484232103/24414062500 : ℝ)^413
        have hw : |(2622544357/5000000000 : ℝ)|=(2622544357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668576741/1250000000 : ℝ)*x 0 + (2622544369/5000000000 : ℝ)*x 1 + (-2106544169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668576741/1250000000 : ℝ)^541 ≤ (22028543514913/50000000000000 : ℝ)^413 := by
    have hnat : (668576741 : ℕ)^541*50000000000000^413 ≤ 22028543514913^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668576741 1250000000 22028543514913 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622544369/5000000000 : ℝ)^541 ≤ (10735853737821/25000000000000 : ℝ)^413 := by
    have hnat : (2622544369 : ℕ)^541*25000000000000^413 ≤ 10735853737821^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622544369 5000000000 10735853737821 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106544169/10000000000 : ℝ)^541 ≤ (2599899599983/20000000000000 : ℝ)^413 := by
    have hnat : (2106544169 : ℕ)^541*20000000000000^413 ≤ 2599899599983^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106544169 10000000000 2599899599983 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668576741/1250000000 : ℝ), (2622544369/5000000000 : ℝ), (-2106544169/10000000000 : ℝ)] ![(22028543514913/50000000000000 : ℝ), (10735853737821/25000000000000 : ℝ), (2599899599983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668576741/1250000000 : ℝ)|^541 ≤ (22028543514913/50000000000000 : ℝ)^413
        have hw : |(668576741/1250000000 : ℝ)|=(668576741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622544369/5000000000 : ℝ)|^541 ≤ (10735853737821/25000000000000 : ℝ)^413
        have hw : |(2622544369/5000000000 : ℝ)|=(2622544369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106544169/10000000000 : ℝ)|^541 ≤ (2599899599983/20000000000000 : ℝ)^413
        have hw : |(-2106544169/10000000000 : ℝ)|=(2106544169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4319845107/10000000000 : ℝ)*x 0 + (4146993077/10000000000 : ℝ)*x 1 + (4499334963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319845107/10000000000 : ℝ)^541 ≤ (33303493162983/100000000000000 : ℝ)^413 := by
    have hnat : (4319845107 : ℕ)^541*100000000000000^413 ≤ 33303493162983^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319845107 10000000000 33303493162983 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146993077/10000000000 : ℝ)^541 ≤ (15784412008617/50000000000000 : ℝ)^413 := by
    have hnat : (4146993077 : ℕ)^541*50000000000000^413 ≤ 15784412008617^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146993077 10000000000 15784412008617 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499334963/10000000000 : ℝ)^541 ≤ (35127682810787/100000000000000 : ℝ)^413 := by
    have hnat : (4499334963 : ℕ)^541*100000000000000^413 ≤ 35127682810787^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499334963 10000000000 35127682810787 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319845107/10000000000 : ℝ), (4146993077/10000000000 : ℝ), (4499334963/10000000000 : ℝ)] ![(33303493162983/100000000000000 : ℝ), (15784412008617/50000000000000 : ℝ), (35127682810787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319845107/10000000000 : ℝ)|^541 ≤ (33303493162983/100000000000000 : ℝ)^413
        have hw : |(4319845107/10000000000 : ℝ)|=(4319845107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146993077/10000000000 : ℝ)|^541 ≤ (15784412008617/50000000000000 : ℝ)^413
        have hw : |(4146993077/10000000000 : ℝ)|=(4146993077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499334963/10000000000 : ℝ)|^541 ≤ (35127682810787/100000000000000 : ℝ)^413
        have hw : |(4499334963/10000000000 : ℝ)|=(4499334963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010847249/5000000000 : ℝ)*x 0 + (1311422063/2500000000 : ℝ)*x 1 + (5411071783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010847249/5000000000 : ℝ)^541 ≤ (1539741405053/12500000000000 : ℝ)^413 := by
    have hnat : (1010847249 : ℕ)^541*12500000000000^413 ≤ 1539741405053^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010847249 5000000000 1539741405053 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311422063/2500000000 : ℝ)^541 ≤ (42949844758803/100000000000000 : ℝ)^413 := by
    have hnat : (1311422063 : ℕ)^541*100000000000000^413 ≤ 42949844758803^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311422063 2500000000 42949844758803 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411071783/10000000000 : ℝ)^541 ≤ (44732223994041/100000000000000 : ℝ)^413 := by
    have hnat : (5411071783 : ℕ)^541*100000000000000^413 ≤ 44732223994041^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411071783 10000000000 44732223994041 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010847249/5000000000 : ℝ), (1311422063/2500000000 : ℝ), (5411071783/10000000000 : ℝ)] ![(1539741405053/12500000000000 : ℝ), (42949844758803/100000000000000 : ℝ), (44732223994041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010847249/5000000000 : ℝ)|^541 ≤ (1539741405053/12500000000000 : ℝ)^413
        have hw : |(-1010847249/5000000000 : ℝ)|=(1010847249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311422063/2500000000 : ℝ)|^541 ≤ (42949844758803/100000000000000 : ℝ)^413
        have hw : |(1311422063/2500000000 : ℝ)|=(1311422063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411071783/10000000000 : ℝ)|^541 ≤ (44732223994041/100000000000000 : ℝ)^413
        have hw : |(5411071783/10000000000 : ℝ)|=(5411071783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061115919/2000000000 : ℝ)*x 0 + (-1940561153/10000000000 : ℝ)*x 1 + (5411071503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061115919/2000000000 : ℝ)^541 ≤ (43593326283811/100000000000000 : ℝ)^413 := by
    have hnat : (1061115919 : ℕ)^541*100000000000000^413 ≤ 43593326283811^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061115919 2000000000 43593326283811 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940561153/10000000000 : ℝ)^541 ≤ (364826647729/3125000000000 : ℝ)^413 := by
    have hnat : (1940561153 : ℕ)^541*3125000000000^413 ≤ 364826647729^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940561153 10000000000 364826647729 3125000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411071503/10000000000 : ℝ)^541 ≤ (11183055240487/25000000000000 : ℝ)^413 := by
    have hnat : (5411071503 : ℕ)^541*25000000000000^413 ≤ 11183055240487^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411071503 10000000000 11183055240487 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061115919/2000000000 : ℝ), (-1940561153/10000000000 : ℝ), (5411071503/10000000000 : ℝ)] ![(43593326283811/100000000000000 : ℝ), (364826647729/3125000000000 : ℝ), (11183055240487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061115919/2000000000 : ℝ)|^541 ≤ (43593326283811/100000000000000 : ℝ)^413
        have hw : |(1061115919/2000000000 : ℝ)|=(1061115919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940561153/10000000000 : ℝ)|^541 ≤ (364826647729/3125000000000 : ℝ)^413
        have hw : |(-1940561153/10000000000 : ℝ)|=(1940561153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411071503/10000000000 : ℝ)|^541 ≤ (11183055240487/25000000000000 : ℝ)^413
        have hw : |(5411071503/10000000000 : ℝ)|=(5411071503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652789979/5000000000 : ℝ)*x 0 + (338191939/625000000 : ℝ)*x 1 + (-1940561317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652789979/5000000000 : ℝ)^541 ≤ (43593330190789/100000000000000 : ℝ)^413 := by
    have hnat : (2652789979 : ℕ)^541*100000000000000^413 ≤ 43593330190789^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652789979 5000000000 43593330190789 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338191939/625000000 : ℝ)^541 ≤ (5591526971863/12500000000000 : ℝ)^413 := by
    have hnat : (338191939 : ℕ)^541*12500000000000^413 ≤ 5591526971863^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338191939 625000000 5591526971863 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1940561317/10000000000 : ℝ)^541 ≤ (11674454019737/100000000000000 : ℝ)^413 := by
    have hnat : (1940561317 : ℕ)^541*100000000000000^413 ≤ 11674454019737^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940561317 10000000000 11674454019737 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652789979/5000000000 : ℝ), (338191939/625000000 : ℝ), (-1940561317/10000000000 : ℝ)] ![(43593330190789/100000000000000 : ℝ), (5591526971863/12500000000000 : ℝ), (11674454019737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652789979/5000000000 : ℝ)|^541 ≤ (43593330190789/100000000000000 : ℝ)^413
        have hw : |(2652789979/5000000000 : ℝ)|=(2652789979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338191939/625000000 : ℝ)|^541 ≤ (5591526971863/12500000000000 : ℝ)^413
        have hw : |(338191939/625000000 : ℝ)|=(338191939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1940561317/10000000000 : ℝ)|^541 ≤ (11674454019737/100000000000000 : ℝ)^413
        have hw : |(-1940561317/10000000000 : ℝ)|=(1940561317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s5_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2159935449/5000000000 : ℝ)*x 0 + (4498066269/10000000000 : ℝ)*x 1 + (2074134003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159935449/5000000000 : ℝ)^541 ≤ (33303753620809/100000000000000 : ℝ)^413 := by
    have hnat : (2159935449 : ℕ)^541*100000000000000^413 ≤ 33303753620809^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159935449 5000000000 33303753620809 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498066269/10000000000 : ℝ)^541 ≤ (35114708440239/100000000000000 : ℝ)^413 := by
    have hnat : (4498066269 : ℕ)^541*100000000000000^413 ≤ 35114708440239^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498066269 10000000000 35114708440239 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074134003/5000000000 : ℝ)^541 ≤ (7895384480803/25000000000000 : ℝ)^413 := by
    have hnat : (2074134003 : ℕ)^541*25000000000000^413 ≤ 7895384480803^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074134003 5000000000 7895384480803 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159935449/5000000000 : ℝ), (4498066269/10000000000 : ℝ), (2074134003/5000000000 : ℝ)] ![(33303753620809/100000000000000 : ℝ), (35114708440239/100000000000000 : ℝ), (7895384480803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159935449/5000000000 : ℝ)|^541 ≤ (33303753620809/100000000000000 : ℝ)^413
        have hw : |(2159935449/5000000000 : ℝ)|=(2159935449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498066269/10000000000 : ℝ)|^541 ≤ (35114708440239/100000000000000 : ℝ)^413
        have hw : |(4498066269/10000000000 : ℝ)|=(4498066269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074134003/5000000000 : ℝ)|^541 ≤ (7895384480803/25000000000000 : ℝ)^413
        have hw : |(2074134003/5000000000 : ℝ)|=(2074134003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11203/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11167/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (9483615351257277/100000000000000000000 : ℝ) := by
    have hpowers : (11167/100000 : ℝ)^4327 ≤ (9483615351257277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11167 : ℕ)^4327*100000000000000000000^1024 ≤ 9483615351257277^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11167 100000 9483615351257277 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11167/100000 : ℝ)) (X := (9483615351257277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (4327/1024 : ℝ) ≤ (7723913414189487/25000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^4327 ≤ (7723913414189487/25000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4327*25000000000000000000^1024 ≤ 7723913414189487^1024*6250^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 7723913414189487 25000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (7723913414189487/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009483615351257277/50000000000000000000 : ℝ) ≤ (5000224416897969/5000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50009483615351257277/50000000000000000000 : ℝ)^1024 ≤ (5000224416897969/5000000000000000 : ℝ)^4327 := by
      have hnat : (50009483615351257277 : ℕ)^1024*5000000000000000^4327 ≤ 5000224416897969^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009483615351257277 50000000000000000000 5000224416897969 5000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000224416897969/5000000000000000 : ℝ)) (X := (50009483615351257277/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001615170760320609/4000000000000000000 : ℝ) ≤ (10000955442581357/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (4001615170760320609/4000000000000000000 : ℝ)^1024 ≤ (10000955442581357/10000000000000000 : ℝ)^4327 := by
      have hnat : (4001615170760320609 : ℕ)^1024*10000000000000000^4327 ≤ 10000955442581357^4327*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001615170760320609 4000000000000000000 10000955442581357 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000955442581357/10000000000000000 : ℝ)) (X := (4001615170760320609/4000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507723913414189487/12500000000000000000 : ℝ) ≤ (1250182756420847/1250000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (12507723913414189487/12500000000000000000 : ℝ)^1024 ≤ (1250182756420847/1250000000000000 : ℝ)^4327 := by
      have hnat : (12507723913414189487 : ℕ)^1024*1250000000000000^4327 ≤ 1250182756420847^4327*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507723913414189487 12500000000000000000 1250182756420847 1250000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250182756420847/1250000000000000 : ℝ)) (X := (12507723913414189487/12500000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9483615351257277/100000000000000000000 : ℝ) ≤ ((346156746633515623/346250000000000000 : ℝ)+2*(506608785419/360100000000000 : ℝ)*(11167/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (346156746633515623/346250000000000000 : ℝ)+2*(506608785419/360100000000000 : ℝ)*(11167/100000 : ℝ)=(5000224416897969/5000000000000000 : ℝ) by norm_num, show 1+2*(9483615351257277/100000000000000000000 : ℝ)=(50009483615351257277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7723913414189487/25000000000000000000 : ℝ)+(9483615351257277/100000000000000000000 : ℝ) ≤ ((346156746633515623/346250000000000000 : ℝ)+(506608785419/360100000000000 : ℝ)*((923/6250 : ℝ)+(11167/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (346156746633515623/346250000000000000 : ℝ)+(506608785419/360100000000000 : ℝ)*((923/6250 : ℝ)+(11167/100000 : ℝ))=(10000955442581357/10000000000000000 : ℝ) by norm_num, show 1+(7723913414189487/25000000000000000000 : ℝ)+(9483615351257277/100000000000000000000 : ℝ)=(4001615170760320609/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7723913414189487/25000000000000000000 : ℝ) ≤ ((346156746633515623/346250000000000000 : ℝ)+2*(506608785419/360100000000000 : ℝ)*(923/6250 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (346156746633515623/346250000000000000 : ℝ)+2*(506608785419/360100000000000 : ℝ)*(923/6250 : ℝ)=(1250182756420847/1250000000000000 : ℝ) by norm_num, show 1+2*(7723913414189487/25000000000000000000 : ℝ)=(12507723913414189487/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (346156746633515623/346250000000000000 : ℝ)*(X 1 0+X 2 0)+(506608785419/360100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (346156746633515623/346250000000000000 : ℝ)) (alpha := (506608785419/360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (346156746633515623/346250000000000000 : ℝ)*(X 0 1+X 2 1)+(506608785419/360100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (346156746633515623/346250000000000000 : ℝ)) (alpha := (506608785419/360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (346156746633515623/346250000000000000 : ℝ)*(X 0 2+X 1 2)+(506608785419/360100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (346156746633515623/346250000000000000 : ℝ)) (alpha := (506608785419/360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-505420561/2500000000 : ℝ)*X 0 0+(1082334911/2000000000 : ℝ)*X 0 1+(4196071/8000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348613873/10000000000 : ℝ)*X 1 0+(-84261771/400000000 : ℝ)*X 1 1+(2622544357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668576741/1250000000 : ℝ)*X 2 0+(2622544369/5000000000 : ℝ)*X 2 1+(-2106544169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319845107/10000000000 : ℝ)*X 0 0+(4146993077/10000000000 : ℝ)*X 0 1+(4499334963/10000000000 : ℝ)*X 0 2+(4319845107/10000000000 : ℝ)*X 1 0+(4146993077/10000000000 : ℝ)*X 1 1+(4499334963/10000000000 : ℝ)*X 1 2+(4319845107/10000000000 : ℝ)*X 2 0+(4146993077/10000000000 : ℝ)*X 2 1+(4499334963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1010847249/5000000000 : ℝ)*X 0 0+(1311422063/2500000000 : ℝ)*X 0 1+(5411071783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061115919/2000000000 : ℝ)*X 1 0+(-1940561153/10000000000 : ℝ)*X 1 1+(5411071503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652789979/5000000000 : ℝ)*X 2 0+(338191939/625000000 : ℝ)*X 2 1+(-1940561317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159935449/5000000000 : ℝ)*X 0 0+(4498066269/10000000000 : ℝ)*X 0 1+(2074134003/5000000000 : ℝ)*X 0 2+(2159935449/5000000000 : ℝ)*X 1 0+(4498066269/10000000000 : ℝ)*X 1 1+(2074134003/5000000000 : ℝ)*X 1 2+(2159935449/5000000000 : ℝ)*X 2 0+(4498066269/10000000000 : ℝ)*X 2 1+(2074134003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (383058134980006480546019211/112531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (260148029/50000000000000 : ℝ)*(base19) + (7412887/1250000000000 : ℝ)*(base23) + (1160411/50000000000000 : ℝ)*(lower2) + (475831/625000000000 : ℝ)*(upper5) + (4420550751575687/100000000000000 : ℝ)*(major0) + (4420550751575687/100000000000000 : ℝ)*(major1) + (4420550751575687/100000000000000 : ℝ)*(major2) + (300146215083073/5000000000000 : ℝ)*(sp0) + (375183586518359/6250000000000 : ℝ)*(sp1) + (300146960940839/5000000000000 : ℝ)*(sp2) + (567631485323851/20000000000000 : ℝ)*(sp3) + (387754657/2500000000000 : ℝ)*(sp4) + (953628969/50000000000000 : ℝ)*(sp5) + (4151217187/100000000000000 : ℝ)*(sp7) + (1419080788918221/50000000000000 : ℝ)*(f.failure) + (300146990592387/5000000000000 : ℝ)*(f.sum) + (2595834836099/9002500000000000000000000000 : ℝ)*base65 + (2094614261667633487/450125000000000000000000000000000 : ℝ)*base68 + (1232057899266241513/450125000000000000000000000000000 : ℝ)*base69 + (1198613203952991513/450125000000000000000000000000000 : ℝ)*base71 + (112060658648267/18005000000000000000000000000 : ℝ)*base74 + (3140032539542491513/450125000000000000000000000000000 : ℝ)*base75 + (1438067902575741513/450125000000000000000000000000000 : ℝ)*base77 + (3383546175984866513/450125000000000000000000000000000 : ℝ)*base79 + (12360201488741/9002500000000000000000000000 : ℝ)*base82 + (1099921/250000000000000000000 : ℝ)*base89 + (1099921/250000000000000000000 : ℝ)*base91 + (1099921/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27380927589580051944785307/4328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (490786501/20000000000000 : ℝ)*(base19) + (2791108693/100000000000000 : ℝ)*(base23) + (7244923/50000000000000 : ℝ)*(upper2) + (16321503/25000000000000 : ℝ)*(upper3) + (363496497/100000000000000 : ℝ)*(upper5) + (556584503108411/12500000000000 : ℝ)*(major0) + (556584503108411/12500000000000 : ℝ)*(major1) + (556584503108411/12500000000000 : ℝ)*(major2) + (53710524099/100000000000000 : ℝ)*(sp1) + (40909735659/100000000000000 : ℝ)*(sp2) + (94477572104749/1562500000000 : ℝ)*(sp4) + (1511627112561833/25000000000000 : ℝ)*(sp5) + (5904805579941/97656250000 : ℝ)*(sp6) + (89337100754833/3125000000000 : ℝ)*(sp7) + (89337100754833/3125000000000 : ℝ)*(f.failure) + (94477572104749/1562500000000 : ℝ)*(f.sum) + (7515357261391/2250625000000000000000000000 : ℝ)*base66 + (747672452659278189/56265625000000000000000000000000 : ℝ)*base67 + (102423020279778189/56265625000000000000000000000000 : ℝ)*base69 + (15757052944728093/28132812500000000000000000000000 : ℝ)*base72 + (71703189392457/18005000000000000000000000000 : ℝ)*base73 + (35564784042371939/56265625000000000000000000000000 : ℝ)*base75 + (619358228784096811/56265625000000000000000000000000 : ℝ)*base78 + (1252282693407934439/56265625000000000000000000000000 : ℝ)*base79 + (67457095399513/18005000000000000000000000000 : ℝ)*base82 + (41067/15625000000000000000 : ℝ)*base90 + (41067/15625000000000000000 : ℝ)*base92 + (41067/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1368_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1368_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1368_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1368_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1368_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3201/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
