-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1602_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:11.436633+00:00
-- url     : https://prove2.me/submissions/b02897af-ef50-49ab-a28d-1b3f92340676

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
theorem support_rectangle_w1602_s3_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-344896221/2000000000 : ℝ)*x 0 + (5462635671/10000000000 : ℝ)*x 1 + (1294843231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344896221/2000000000 : ℝ)^4727 ≤ (10606440472557/100000000000000 : ℝ)^3703 := by
    have hnat : (344896221 : ℕ)^4727*100000000000000^3703 ≤ 10606440472557^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344896221 2000000000 10606440472557 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462635671/10000000000 : ℝ)^4727 ≤ (23107630467003/50000000000000 : ℝ)^3703 := by
    have hnat : (5462635671 : ℕ)^4727*50000000000000^3703 ≤ 23107630467003^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462635671 10000000000 23107630467003 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294843231/2500000000 : ℝ)^4727 ≤ (2698643661489/6250000000000 : ℝ)^3703 := by
    have hnat : (1294843231 : ℕ)^4727*6250000000000^3703 ≤ 2698643661489^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294843231 2500000000 2698643661489 6250000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344896221/2000000000 : ℝ), (5462635671/10000000000 : ℝ), (1294843231/2500000000 : ℝ)] ![(10606440472557/100000000000000 : ℝ), (23107630467003/50000000000000 : ℝ), (2698643661489/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344896221/2000000000 : ℝ)|^4727 ≤ (10606440472557/100000000000000 : ℝ)^3703
        have hw : |(-344896221/2000000000 : ℝ)|=(344896221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462635671/10000000000 : ℝ)|^4727 ≤ (23107630467003/50000000000000 : ℝ)^3703
        have hw : |(5462635671/10000000000 : ℝ)|=(5462635671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294843231/2500000000 : ℝ)|^4727 ≤ (2698643661489/6250000000000 : ℝ)^3703
        have hw : |(1294843231/2500000000 : ℝ)|=(1294843231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669359939/1250000000 : ℝ)*x 0 + (-935309447/5000000000 : ℝ)*x 1 + (5179372877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669359939/1250000000 : ℝ)^4727 ≤ (45054706983919/100000000000000 : ℝ)^3703 := by
    have hnat : (669359939 : ℕ)^4727*100000000000000^3703 ≤ 45054706983919^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669359939 1250000000 45054706983919 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935309447/5000000000 : ℝ)^4727 ≤ (11766994925237/100000000000000 : ℝ)^3703 := by
    have hnat : (935309447 : ℕ)^4727*100000000000000^3703 ≤ 11766994925237^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935309447 5000000000 11766994925237 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179372877/10000000000 : ℝ)^4727 ≤ (43178298083653/100000000000000 : ℝ)^3703 := by
    have hnat : (5179372877 : ℕ)^4727*100000000000000^3703 ≤ 43178298083653^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179372877 10000000000 43178298083653 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669359939/1250000000 : ℝ), (-935309447/5000000000 : ℝ), (5179372877/10000000000 : ℝ)] ![(45054706983919/100000000000000 : ℝ), (11766994925237/100000000000000 : ℝ), (43178298083653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669359939/1250000000 : ℝ)|^4727 ≤ (45054706983919/100000000000000 : ℝ)^3703
        have hw : |(669359939/1250000000 : ℝ)|=(669359939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935309447/5000000000 : ℝ)|^4727 ≤ (11766994925237/100000000000000 : ℝ)^3703
        have hw : |(-935309447/5000000000 : ℝ)|=(935309447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179372877/10000000000 : ℝ)|^4727 ≤ (43178298083653/100000000000000 : ℝ)^3703
        have hw : |(5179372877/10000000000 : ℝ)|=(5179372877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354879537/10000000000 : ℝ)*x 0 + (2589686417/5000000000 : ℝ)*x 1 + (-467654729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354879537/10000000000 : ℝ)^4727 ≤ (4505470725243/10000000000000 : ℝ)^3703 := by
    have hnat : (5354879537 : ℕ)^4727*10000000000000^3703 ≤ 4505470725243^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354879537 10000000000 4505470725243 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589686417/5000000000 : ℝ)^4727 ≤ (863565952521/2000000000000 : ℝ)^3703 := by
    have hnat : (2589686417 : ℕ)^4727*2000000000000^3703 ≤ 863565952521^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589686417 5000000000 863565952521 2000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467654729/2500000000 : ℝ)^4727 ≤ (2353399020379/20000000000000 : ℝ)^3703 := by
    have hnat : (467654729 : ℕ)^4727*20000000000000^3703 ≤ 2353399020379^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467654729 2500000000 2353399020379 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354879537/10000000000 : ℝ), (2589686417/5000000000 : ℝ), (-467654729/2500000000 : ℝ)] ![(4505470725243/10000000000000 : ℝ), (863565952521/2000000000000 : ℝ), (2353399020379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354879537/10000000000 : ℝ)|^4727 ≤ (4505470725243/10000000000000 : ℝ)^3703
        have hw : |(5354879537/10000000000 : ℝ)|=(5354879537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589686417/5000000000 : ℝ)|^4727 ≤ (863565952521/2000000000000 : ℝ)^3703
        have hw : |(2589686417/5000000000 : ℝ)|=(2589686417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467654729/2500000000 : ℝ)|^4727 ≤ (2353399020379/20000000000000 : ℝ)^3703
        have hw : |(-467654729/2500000000 : ℝ)|=(467654729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219096543/10000000000 : ℝ)*x 0 + (485710033/1250000000 : ℝ)*x 1 + (4574426949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219096543/10000000000 : ℝ)^4727 ≤ (33233834205547/100000000000000 : ℝ)^3703 := by
    have hnat : (4219096543 : ℕ)^4727*100000000000000^3703 ≤ 33233834205547^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219096543 10000000000 33233834205547 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485710033/1250000000 : ℝ)^4727 ≤ (29918605326983/100000000000000 : ℝ)^3703 := by
    have hnat : (485710033 : ℕ)^4727*100000000000000^3703 ≤ 29918605326983^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485710033 1250000000 29918605326983 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4574426949/10000000000 : ℝ)^4727 ≤ (3684756045803/10000000000000 : ℝ)^3703 := by
    have hnat : (4574426949 : ℕ)^4727*10000000000000^3703 ≤ 3684756045803^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574426949 10000000000 3684756045803 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219096543/10000000000 : ℝ), (485710033/1250000000 : ℝ), (4574426949/10000000000 : ℝ)] ![(33233834205547/100000000000000 : ℝ), (29918605326983/100000000000000 : ℝ), (3684756045803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219096543/10000000000 : ℝ)|^4727 ≤ (33233834205547/100000000000000 : ℝ)^3703
        have hw : |(4219096543/10000000000 : ℝ)|=(4219096543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(485710033/1250000000 : ℝ)|^4727 ≤ (29918605326983/100000000000000 : ℝ)^3703
        have hw : |(485710033/1250000000 : ℝ)|=(485710033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4574426949/10000000000 : ℝ)|^4727 ≤ (3684756045803/10000000000000 : ℝ)^3703
        have hw : |(4574426949/10000000000 : ℝ)|=(4574426949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1724553827/10000000000 : ℝ)*x 0 + (2590740209/5000000000 : ℝ)*x 1 + (2730252941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1724553827/10000000000 : ℝ)^4727 ≤ (2121402288029/20000000000000 : ℝ)^3703 := by
    have hnat : (1724553827 : ℕ)^4727*20000000000000^3703 ≤ 2121402288029^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724553827 10000000000 2121402288029 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590740209/5000000000 : ℝ)^4727 ≤ (43200727640629/100000000000000 : ℝ)^3703 := by
    have hnat : (2590740209 : ℕ)^4727*100000000000000^3703 ≤ 43200727640629^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590740209 5000000000 43200727640629 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730252941/5000000000 : ℝ)^4727 ≤ (46192260913227/100000000000000 : ℝ)^3703 := by
    have hnat : (2730252941 : ℕ)^4727*100000000000000^3703 ≤ 46192260913227^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730252941 5000000000 46192260913227 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1724553827/10000000000 : ℝ), (2590740209/5000000000 : ℝ), (2730252941/5000000000 : ℝ)] ![(2121402288029/20000000000000 : ℝ), (43200727640629/100000000000000 : ℝ), (46192260913227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1724553827/10000000000 : ℝ)|^4727 ≤ (2121402288029/20000000000000 : ℝ)^3703
        have hw : |(-1724553827/10000000000 : ℝ)|=(1724553827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590740209/5000000000 : ℝ)|^4727 ≤ (43200727640629/100000000000000 : ℝ)^3703
        have hw : |(2590740209/5000000000 : ℝ)|=(2590740209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730252941/5000000000 : ℝ)|^4727 ≤ (46192260913227/100000000000000 : ℝ)^3703
        have hw : |(2730252941/5000000000 : ℝ)|=(2730252941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279763197/10000000000 : ℝ)*x 0 + (-1589485931/10000000000 : ℝ)*x 1 + (1365126459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279763197/10000000000 : ℝ)^4727 ≤ (8849898860883/20000000000000 : ℝ)^3703 := by
    have hnat : (5279763197 : ℕ)^4727*20000000000000^3703 ≤ 8849898860883^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279763197 10000000000 8849898860883 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1589485931/10000000000 : ℝ)^4727 ≤ (9558245267063/100000000000000 : ℝ)^3703 := by
    have hnat : (1589485931 : ℕ)^4727*100000000000000^3703 ≤ 9558245267063^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589485931 10000000000 9558245267063 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365126459/2500000000 : ℝ)^4727 ≤ (46192260416491/100000000000000 : ℝ)^3703 := by
    have hnat : (1365126459 : ℕ)^4727*100000000000000^3703 ≤ 46192260416491^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365126459 2500000000 46192260416491 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279763197/10000000000 : ℝ), (-1589485931/10000000000 : ℝ), (1365126459/2500000000 : ℝ)] ![(8849898860883/20000000000000 : ℝ), (9558245267063/100000000000000 : ℝ), (46192260416491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279763197/10000000000 : ℝ)|^4727 ≤ (8849898860883/20000000000000 : ℝ)^3703
        have hw : |(5279763197/10000000000 : ℝ)|=(5279763197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1589485931/10000000000 : ℝ)|^4727 ≤ (9558245267063/100000000000000 : ℝ)^3703
        have hw : |(-1589485931/10000000000 : ℝ)|=(1589485931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365126459/2500000000 : ℝ)|^4727 ≤ (46192260416491/100000000000000 : ℝ)^3703
        have hw : |(1365126459/2500000000 : ℝ)|=(1365126459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659970389/1250000000 : ℝ)*x 0 + (5460505879/10000000000 : ℝ)*x 1 + (-158948599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659970389/1250000000 : ℝ)^4727 ≤ (11062373348759/25000000000000 : ℝ)^3703 := by
    have hnat : (659970389 : ℕ)^4727*25000000000000^3703 ≤ 11062373348759^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659970389 1250000000 11062373348759 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460505879/10000000000 : ℝ)^4727 ≤ (46192260880831/100000000000000 : ℝ)^3703 := by
    have hnat : (5460505879 : ℕ)^4727*100000000000000^3703 ≤ 46192260880831^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460505879 10000000000 46192260880831 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158948599/1000000000 : ℝ)^4727 ≤ (9558245719967/100000000000000 : ℝ)^3703 := by
    have hnat : (158948599 : ℕ)^4727*100000000000000^3703 ≤ 9558245719967^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158948599 1000000000 9558245719967 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659970389/1250000000 : ℝ), (5460505879/10000000000 : ℝ), (-158948599/1000000000 : ℝ)] ![(11062373348759/25000000000000 : ℝ), (46192260880831/100000000000000 : ℝ), (9558245719967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659970389/1250000000 : ℝ)|^4727 ≤ (11062373348759/25000000000000 : ℝ)^3703
        have hw : |(659970389/1250000000 : ℝ)|=(659970389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460505879/10000000000 : ℝ)|^4727 ≤ (46192260880831/100000000000000 : ℝ)^3703
        have hw : |(5460505879/10000000000 : ℝ)|=(5460505879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-158948599/1000000000 : ℝ)|^4727 ≤ (9558245719967/100000000000000 : ℝ)^3703
        have hw : |(-158948599/1000000000 : ℝ)|=(158948599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s3_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2109636573/5000000000 : ℝ)*x 0 + (4569302357/10000000000 : ℝ)*x 1 + (972714737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109636573/5000000000 : ℝ)^4727 ≤ (33235610003153/100000000000000 : ℝ)^3703 := by
    have hnat : (2109636573 : ℕ)^4727*100000000000000^3703 ≤ 33235610003153^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109636573 5000000000 33235610003153 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4569302357/10000000000 : ℝ)^4727 ≤ (9198718593069/25000000000000 : ℝ)^3703 := by
    have hnat : (4569302357 : ℕ)^4727*25000000000000^3703 ≤ 9198718593069^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569302357 10000000000 9198718593069 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (972714737/2500000000 : ℝ)^4727 ≤ (14984757809137/50000000000000 : ℝ)^3703 := by
    have hnat : (972714737 : ℕ)^4727*50000000000000^3703 ≤ 14984757809137^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972714737 2500000000 14984757809137 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109636573/5000000000 : ℝ), (4569302357/10000000000 : ℝ), (972714737/2500000000 : ℝ)] ![(33235610003153/100000000000000 : ℝ), (9198718593069/25000000000000 : ℝ), (14984757809137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109636573/5000000000 : ℝ)|^4727 ≤ (33235610003153/100000000000000 : ℝ)^3703
        have hw : |(2109636573/5000000000 : ℝ)|=(2109636573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4569302357/10000000000 : ℝ)|^4727 ≤ (9198718593069/25000000000000 : ℝ)^3703
        have hw : |(4569302357/10000000000 : ℝ)|=(4569302357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(972714737/2500000000 : ℝ)|^4727 ≤ (14984757809137/50000000000000 : ℝ)^3703
        have hw : |(972714737/2500000000 : ℝ)|=(972714737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1637/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (409/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (409/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (409/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (409/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (409/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (409/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (409/4000 : ℝ) ^ (4723/1024 : ℝ) ≤ (1352805865636889/50000000000000000000 : ℝ) := by
    have hpowers : (409/4000 : ℝ)^4723 ≤ (1352805865636889/50000000000000000000 : ℝ)^1024 := by
      have hnat : (409 : ℕ)^4723*50000000000000000000^1024 ≤ 1352805865636889^1024*4000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        409 4000 1352805865636889 50000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (409/4000 : ℝ)) (X := (1352805865636889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16529/100000 : ℝ) ^ (4723/1024 : ℝ) ≤ (24792198185393569/100000000000000000000 : ℝ) := by
    have hpowers : (16529/100000 : ℝ)^4723 ≤ (24792198185393569/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16529 : ℕ)^4723*100000000000000000000^1024 ≤ 24792198185393569^1024*100000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16529 100000 24792198185393569 100000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16529/100000 : ℝ)) (X := (24792198185393569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001352805865636889/25000000000000000000 : ℝ) ≤ (10000117318979747/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (25001352805865636889/25000000000000000000 : ℝ)^1024 ≤ (10000117318979747/10000000000000000 : ℝ)^4723 := by
      have hnat : (25001352805865636889 : ℕ)^1024*10000000000000000^4723 ≤ 10000117318979747^4723*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001352805865636889 25000000000000000000 10000117318979747 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000117318979747/10000000000000000 : ℝ)) (X := (25001352805865636889/25000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027497809916667347/100000000000000000000 : ℝ) ≤ (5000298059769497/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (100027497809916667347/100000000000000000000 : ℝ)^1024 ≤ (5000298059769497/5000000000000000 : ℝ)^4723 := by
      have hnat : (100027497809916667347 : ℕ)^1024*5000000000000000^4723 ≤ 5000298059769497^4723*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027497809916667347 100000000000000000000 5000298059769497 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000298059769497/5000000000000000 : ℝ)) (X := (100027497809916667347/100000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024792198185393569/50000000000000000000 : ℝ) ≤ (10001074920098241/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (50024792198185393569/50000000000000000000 : ℝ)^1024 ≤ (10001074920098241/10000000000000000 : ℝ)^4723 := by
      have hnat : (50024792198185393569 : ℕ)^1024*10000000000000000^4723 ≤ 10001074920098241^4723*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024792198185393569 50000000000000000000 10001074920098241 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001074920098241/10000000000000000 : ℝ)) (X := (50024792198185393569/50000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1352805865636889/50000000000000000000 : ℝ) ≤ ((31515474053705861969/31520000000000000000 : ℝ)+2*(478800559247/630400000000000 : ℝ)*(409/4000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (31515474053705861969/31520000000000000000 : ℝ)+2*(478800559247/630400000000000 : ℝ)*(409/4000 : ℝ)=(10000117318979747/10000000000000000 : ℝ) by norm_num, show 1+2*(1352805865636889/50000000000000000000 : ℝ)=(25001352805865636889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24792198185393569/100000000000000000000 : ℝ)+(1352805865636889/50000000000000000000 : ℝ) ≤ ((31515474053705861969/31520000000000000000 : ℝ)+(478800559247/630400000000000 : ℝ)*((16529/100000 : ℝ)+(409/4000 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (31515474053705861969/31520000000000000000 : ℝ)+(478800559247/630400000000000 : ℝ)*((16529/100000 : ℝ)+(409/4000 : ℝ))=(5000298059769497/5000000000000000 : ℝ) by norm_num, show 1+(24792198185393569/100000000000000000000 : ℝ)+(1352805865636889/50000000000000000000 : ℝ)=(100027497809916667347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24792198185393569/100000000000000000000 : ℝ) ≤ ((31515474053705861969/31520000000000000000 : ℝ)+2*(478800559247/630400000000000 : ℝ)*(16529/100000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (31515474053705861969/31520000000000000000 : ℝ)+2*(478800559247/630400000000000 : ℝ)*(16529/100000 : ℝ)=(10001074920098241/10000000000000000 : ℝ) by norm_num, show 1+2*(24792198185393569/100000000000000000000 : ℝ)=(50024792198185393569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31515474053705861969/31520000000000000000 : ℝ)*(X 1 0+X 2 0)+(478800559247/630400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (409/4000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (31515474053705861969/31520000000000000000 : ℝ)) (alpha := (478800559247/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31515474053705861969/31520000000000000000 : ℝ)*(X 0 1+X 2 1)+(478800559247/630400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (409/4000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (31515474053705861969/31520000000000000000 : ℝ)) (alpha := (478800559247/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31515474053705861969/31520000000000000000 : ℝ)*(X 0 2+X 1 2)+(478800559247/630400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (409/4000 : ℝ)) (hi := (16529/100000 : ℝ)) (c := (31515474053705861969/31520000000000000000 : ℝ)) (alpha := (478800559247/630400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-344896221/2000000000 : ℝ)*X 0 0+(5462635671/10000000000 : ℝ)*X 0 1+(1294843231/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669359939/1250000000 : ℝ)*X 1 0+(-935309447/5000000000 : ℝ)*X 1 1+(5179372877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354879537/10000000000 : ℝ)*X 2 0+(2589686417/5000000000 : ℝ)*X 2 1+(-467654729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4219096543/10000000000 : ℝ)*X 0 0+(485710033/1250000000 : ℝ)*X 0 1+(4574426949/10000000000 : ℝ)*X 0 2+(4219096543/10000000000 : ℝ)*X 1 0+(485710033/1250000000 : ℝ)*X 1 1+(4574426949/10000000000 : ℝ)*X 1 2+(4219096543/10000000000 : ℝ)*X 2 0+(485710033/1250000000 : ℝ)*X 2 1+(4574426949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1724553827/10000000000 : ℝ)*X 0 0+(2590740209/5000000000 : ℝ)*X 0 1+(2730252941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279763197/10000000000 : ℝ)*X 1 0+(-1589485931/10000000000 : ℝ)*X 1 1+(1365126459/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659970389/1250000000 : ℝ)*X 2 0+(5460505879/10000000000 : ℝ)*X 2 1+(-158948599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109636573/5000000000 : ℝ)*X 0 0+(4569302357/10000000000 : ℝ)*X 0 1+(972714737/2500000000 : ℝ)*X 0 2+(2109636573/5000000000 : ℝ)*X 1 0+(4569302357/10000000000 : ℝ)*X 1 1+(972714737/2500000000 : ℝ)*X 1 2+(2109636573/5000000000 : ℝ)*X 2 0+(4569302357/10000000000 : ℝ)*X 2 1+(972714737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21292239754779434887881/1970000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1871235887/100000000000000 : ℝ)*(base19) + (1730736169/100000000000000 : ℝ)*(base23) + (84061739/100000000000000 : ℝ)*(lower2) + (36382971/12500000000000 : ℝ)*(upper3) + (40310457/25000000000000 : ℝ)*(upper5) + (155695826295043/6250000000000 : ℝ)*(major0) + (155695826295043/6250000000000 : ℝ)*(major1) + (155695826295043/6250000000000 : ℝ)*(major2) + (1765156871346057/50000000000000 : ℝ)*(sp0) + (3530333014359907/100000000000000 : ℝ)*(sp1) + (28242665238877/800000000000 : ℝ)*(sp2) + (290384226880721/20000000000000 : ℝ)*(sp3) + (21142903681/100000000000000 : ℝ)*(sp4) + (5030583593/50000000000000 : ℝ)*(sp7) + (181491399446349/12500000000000 : ℝ)*(f.failure) + (1765167442797897/50000000000000 : ℝ)*(f.sum) + (7596720330041/1970000000000000000000000000 : ℝ)*base65 + (39985500320030333/197000000000000000000000000000000 : ℝ)*base68 + (1067730201189030333/197000000000000000000000000000000 : ℝ)*base70 + (249915014822969667/197000000000000000000000000000000 : ℝ)*base71 + (13452457172541/1970000000000000000000000000 : ℝ)*base73 + (300992414993969667/197000000000000000000000000000000 : ℝ)*base75 + (204315771345969667/197000000000000000000000000000000 : ℝ)*base77 + (1328367489626030333/197000000000000000000000000000000 : ℝ)*base80 + (10088408915811/1970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5682871/1250000000000000000000 : ℝ)*base89 + (5682871/1250000000000000000000 : ℝ)*base91 + (5682871/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2398209225146657478716555271/394000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (517730077/50000000000000 : ℝ)*(base19) + (1015267247/100000000000000 : ℝ)*(base23) + (16125431/12500000000000 : ℝ)*(upper3) + (24986293/100000000000000 : ℝ)*(lower4) + (150739151/100000000000000 : ℝ)*(upper5) + (632233031294653/25000000000000 : ℝ)*(major0) + (632233031294653/25000000000000 : ℝ)*(major1) + (632233031294653/25000000000000 : ℝ)*(major2) + (11544613491/100000000000000 : ℝ)*(sp1) + (10854400137/100000000000000 : ℝ)*(sp2) + (447987768991793/12500000000000 : ℝ)*(sp4) + (35838895718607/1000000000000 : ℝ)*(sp5) + (44798628528337/1250000000000 : ℝ)*(sp6) + (736980947764347/50000000000000 : ℝ)*(sp7) + (736980947764347/50000000000000 : ℝ)*(f.failure) + (447987768991793/12500000000000 : ℝ)*(f.sum) + (1079352138611/7880000000000000000000000000 : ℝ)*base65 + (992363217699698243/788000000000000000000000000000000 : ℝ)*base68 + (1718314340459698243/788000000000000000000000000000000 : ℝ)*base70 + (7409136706292301757/788000000000000000000000000000000 : ℝ)*base71 + (40313533493229/7880000000000000000000000000 : ℝ)*base74 + (2800173250871698243/788000000000000000000000000000000 : ℝ)*base76 + (3003963130256301757/788000000000000000000000000000000 : ℝ)*base77 + (372569938827698243/788000000000000000000000000000000 : ℝ)*base80 + (47042666711309/7880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16257313/5000000000000000000000 : ℝ)*base89 + (16257313/5000000000000000000000 : ℝ)*base91 + (16257313/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1602_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1602_s4_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431155647/2500000000 : ℝ)*x 0 + (1092387093/2000000000 : ℝ)*x 1 + (517997911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431155647/2500000000 : ℝ)^4727 ≤ (5303775657283/50000000000000 : ℝ)^3703 := by
    have hnat : (431155647 : ℕ)^4727*50000000000000^3703 ≤ 5303775657283^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431155647 2500000000 5303775657283 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092387093/2000000000 : ℝ)^4727 ≤ (9241539798917/20000000000000 : ℝ)^3703 := by
    have hnat : (1092387093 : ℕ)^4727*20000000000000^3703 ≤ 9241539798917^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092387093 2000000000 9241539798917 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517997911/1000000000 : ℝ)^4727 ≤ (10796187418687/25000000000000 : ℝ)^3703 := by
    have hnat : (517997911 : ℕ)^4727*25000000000000^3703 ≤ 10796187418687^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517997911 1000000000 10796187418687 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431155647/2500000000 : ℝ), (1092387093/2000000000 : ℝ), (517997911/1000000000 : ℝ)] ![(5303775657283/50000000000000 : ℝ), (9241539798917/20000000000000 : ℝ), (10796187418687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431155647/2500000000 : ℝ)|^4727 ≤ (5303775657283/50000000000000 : ℝ)^3703
        have hw : |(-431155647/2500000000 : ℝ)|=(431155647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092387093/2000000000 : ℝ)|^4727 ≤ (9241539798917/20000000000000 : ℝ)^3703
        have hw : |(1092387093/2000000000 : ℝ)|=(1092387093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517997911/1000000000 : ℝ)|^4727 ≤ (10796187418687/25000000000000 : ℝ)^3703
        have hw : |(517997911/1000000000 : ℝ)|=(517997911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354692391/10000000000 : ℝ)*x 0 + (-935032857/5000000000 : ℝ)*x 1 + (1294994777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354692391/10000000000 : ℝ)^4727 ≤ (22526348615223/50000000000000 : ℝ)^3703 := by
    have hnat : (5354692391 : ℕ)^4727*50000000000000^3703 ≤ 22526348615223^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354692391 10000000000 22526348615223 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935032857/5000000000 : ℝ)^4727 ≤ (5881276553153/50000000000000 : ℝ)^3703 := by
    have hnat : (935032857 : ℕ)^4727*50000000000000^3703 ≤ 5881276553153^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935032857 5000000000 5881276553153 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294994777/2500000000 : ℝ)^4727 ≤ (5398093706683/12500000000000 : ℝ)^3703 := by
    have hnat : (1294994777 : ℕ)^4727*12500000000000^3703 ≤ 5398093706683^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294994777 2500000000 5398093706683 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354692391/10000000000 : ℝ), (-935032857/5000000000 : ℝ), (1294994777/2500000000 : ℝ)] ![(22526348615223/50000000000000 : ℝ), (5881276553153/50000000000000 : ℝ), (5398093706683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354692391/10000000000 : ℝ)|^4727 ≤ (22526348615223/50000000000000 : ℝ)^3703
        have hw : |(5354692391/10000000000 : ℝ)|=(5354692391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935032857/5000000000 : ℝ)|^4727 ≤ (5881276553153/50000000000000 : ℝ)^3703
        have hw : |(-935032857/5000000000 : ℝ)|=(935032857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294994777/2500000000 : ℝ)|^4727 ≤ (5398093706683/12500000000000 : ℝ)^3703
        have hw : |(1294994777/2500000000 : ℝ)|=(1294994777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535469239/1000000000 : ℝ)*x 0 + (5179979109/10000000000 : ℝ)*x 1 + (-1870065713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535469239/1000000000 : ℝ)^4727 ≤ (22526348609853/50000000000000 : ℝ)^3703 := by
    have hnat : (535469239 : ℕ)^4727*50000000000000^3703 ≤ 22526348609853^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535469239 1000000000 22526348609853 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179979109/10000000000 : ℝ)^4727 ≤ (21592374832053/50000000000000 : ℝ)^3703 := by
    have hnat : (5179979109 : ℕ)^4727*50000000000000^3703 ≤ 21592374832053^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179979109 10000000000 21592374832053 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870065713/10000000000 : ℝ)^4727 ≤ (11762553098277/100000000000000 : ℝ)^3703 := by
    have hnat : (1870065713 : ℕ)^4727*100000000000000^3703 ≤ 11762553098277^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870065713 10000000000 11762553098277 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535469239/1000000000 : ℝ), (5179979109/10000000000 : ℝ), (-1870065713/10000000000 : ℝ)] ![(22526348609853/50000000000000 : ℝ), (21592374832053/50000000000000 : ℝ), (11762553098277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535469239/1000000000 : ℝ)|^4727 ≤ (22526348609853/50000000000000 : ℝ)^3703
        have hw : |(535469239/1000000000 : ℝ)|=(535469239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179979109/10000000000 : ℝ)|^4727 ≤ (21592374832053/50000000000000 : ℝ)^3703
        have hw : |(5179979109/10000000000 : ℝ)|=(5179979109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870065713/10000000000 : ℝ)|^4727 ≤ (11762553098277/100000000000000 : ℝ)^3703
        have hw : |(-1870065713/10000000000 : ℝ)|=(1870065713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219187481/10000000000 : ℝ)*x 0 + (3887258891/10000000000 : ℝ)*x 1 + (914565777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219187481/10000000000 : ℝ)^4727 ≤ (33234748612603/100000000000000 : ℝ)^3703 := by
    have hnat : (4219187481 : ℕ)^4727*100000000000000^3703 ≤ 33234748612603^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219187481 10000000000 33234748612603 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3887258891/10000000000 : ℝ)^4727 ≤ (29934122410321/100000000000000 : ℝ)^3703 := by
    have hnat : (3887258891 : ℕ)^4727*100000000000000^3703 ≤ 29934122410321^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887258891 10000000000 29934122410321 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914565777/2000000000 : ℝ)^4727 ≤ (9207782240351/25000000000000 : ℝ)^3703 := by
    have hnat : (914565777 : ℕ)^4727*25000000000000^3703 ≤ 9207782240351^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914565777 2000000000 9207782240351 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219187481/10000000000 : ℝ), (3887258891/10000000000 : ℝ), (914565777/2000000000 : ℝ)] ![(33234748612603/100000000000000 : ℝ), (29934122410321/100000000000000 : ℝ), (9207782240351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219187481/10000000000 : ℝ)|^4727 ≤ (33234748612603/100000000000000 : ℝ)^3703
        have hw : |(4219187481/10000000000 : ℝ)|=(4219187481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3887258891/10000000000 : ℝ)|^4727 ≤ (29934122410321/100000000000000 : ℝ)^3703
        have hw : |(3887258891/10000000000 : ℝ)|=(3887258891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914565777/2000000000 : ℝ)|^4727 ≤ (9207782240351/25000000000000 : ℝ)^3703
        have hw : |(914565777/2000000000 : ℝ)|=(914565777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215586779/1250000000 : ℝ)*x 0 + (5182067383/10000000000 : ℝ)*x 1 + (5459825261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215586779/1250000000 : ℝ)^4727 ≤ (5304056915543/50000000000000 : ℝ)^3703 := by
    have hnat : (215586779 : ℕ)^4727*50000000000000^3703 ≤ 5304056915543^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215586779 1250000000 5304056915543 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182067383/10000000000 : ℝ)^4727 ≤ (21603487439653/50000000000000 : ℝ)^3703 := by
    have hnat : (5182067383 : ℕ)^4727*50000000000000^3703 ≤ 21603487439653^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182067383 10000000000 21603487439653 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459825261/10000000000 : ℝ)^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703 := by
    have hnat : (5459825261 : ℕ)^4727*100000000000000^3703 ≤ 46184911272831^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459825261 10000000000 46184911272831 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215586779/1250000000 : ℝ), (5182067383/10000000000 : ℝ), (5459825261/10000000000 : ℝ)] ![(5304056915543/50000000000000 : ℝ), (21603487439653/50000000000000 : ℝ), (46184911272831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215586779/1250000000 : ℝ)|^4727 ≤ (5304056915543/50000000000000 : ℝ)^3703
        have hw : |(-215586779/1250000000 : ℝ)|=(215586779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182067383/10000000000 : ℝ)|^4727 ≤ (21603487439653/50000000000000 : ℝ)^3703
        have hw : |(5182067383/10000000000 : ℝ)|=(5182067383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459825261/10000000000 : ℝ)|^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703
        have hw : |(5459825261/10000000000 : ℝ)|=(5459825261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659990463/1250000000 : ℝ)*x 0 + (-1590219561/10000000000 : ℝ)*x 1 + (5459825261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659990463/1250000000 : ℝ)^4727 ≤ (44251211507107/100000000000000 : ℝ)^3703 := by
    have hnat : (659990463 : ℕ)^4727*100000000000000^3703 ≤ 44251211507107^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659990463 1250000000 44251211507107 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590219561/10000000000 : ℝ)^4727 ≤ (9563877208969/100000000000000 : ℝ)^3703 := by
    have hnat : (1590219561 : ℕ)^4727*100000000000000^3703 ≤ 9563877208969^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590219561 10000000000 9563877208969 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459825261/10000000000 : ℝ)^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703 := by
    have hnat : (5459825261 : ℕ)^4727*100000000000000^3703 ≤ 46184911272831^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459825261 10000000000 46184911272831 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659990463/1250000000 : ℝ), (-1590219561/10000000000 : ℝ), (5459825261/10000000000 : ℝ)] ![(44251211507107/100000000000000 : ℝ), (9563877208969/100000000000000 : ℝ), (46184911272831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659990463/1250000000 : ℝ)|^4727 ≤ (44251211507107/100000000000000 : ℝ)^3703
        have hw : |(659990463/1250000000 : ℝ)|=(659990463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590219561/10000000000 : ℝ)|^4727 ≤ (9563877208969/100000000000000 : ℝ)^3703
        have hw : |(-1590219561/10000000000 : ℝ)|=(1590219561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459825261/10000000000 : ℝ)|^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703
        have hw : |(5459825261/10000000000 : ℝ)|=(5459825261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659990463/1250000000 : ℝ)*x 0 + (5459825261/10000000000 : ℝ)*x 1 + (-1590219561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659990463/1250000000 : ℝ)^4727 ≤ (44251211507107/100000000000000 : ℝ)^3703 := by
    have hnat : (659990463 : ℕ)^4727*100000000000000^3703 ≤ 44251211507107^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659990463 1250000000 44251211507107 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459825261/10000000000 : ℝ)^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703 := by
    have hnat : (5459825261 : ℕ)^4727*100000000000000^3703 ≤ 46184911272831^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459825261 10000000000 46184911272831 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1590219561/10000000000 : ℝ)^4727 ≤ (9563877208969/100000000000000 : ℝ)^3703 := by
    have hnat : (1590219561 : ℕ)^4727*100000000000000^3703 ≤ 9563877208969^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590219561 10000000000 9563877208969 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659990463/1250000000 : ℝ), (5459825261/10000000000 : ℝ), (-1590219561/10000000000 : ℝ)] ![(44251211507107/100000000000000 : ℝ), (46184911272831/100000000000000 : ℝ), (9563877208969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659990463/1250000000 : ℝ)|^4727 ≤ (44251211507107/100000000000000 : ℝ)^3703
        have hw : |(659990463/1250000000 : ℝ)|=(659990463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459825261/10000000000 : ℝ)|^4727 ≤ (46184911272831/100000000000000 : ℝ)^3703
        have hw : |(5459825261/10000000000 : ℝ)|=(5459825261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1590219561/10000000000 : ℝ)|^4727 ≤ (9563877208969/100000000000000 : ℝ)^3703
        have hw : |(-1590219561/10000000000 : ℝ)|=(1590219561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s4_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52742021/125000000 : ℝ)*x 0 + (2283875649/5000000000 : ℝ)*x 1 + (3892389801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52742021/125000000 : ℝ)^4727 ≤ (664730004951/2000000000000 : ℝ)^3703 := by
    have hnat : (52742021 : ℕ)^4727*2000000000000^3703 ≤ 664730004951^3703*125000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52742021 125000000 664730004951 2000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283875649/5000000000 : ℝ)^4727 ≤ (36778931107809/100000000000000 : ℝ)^3703 := by
    have hnat : (2283875649 : ℕ)^4727*100000000000000^3703 ≤ 36778931107809^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283875649 5000000000 36778931107809 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3892389801/10000000000 : ℝ)^4727 ≤ (7496142156111/25000000000000 : ℝ)^3703 := by
    have hnat : (3892389801 : ℕ)^4727*25000000000000^3703 ≤ 7496142156111^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892389801 10000000000 7496142156111 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52742021/125000000 : ℝ), (2283875649/5000000000 : ℝ), (3892389801/10000000000 : ℝ)] ![(664730004951/2000000000000 : ℝ), (36778931107809/100000000000000 : ℝ), (7496142156111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52742021/125000000 : ℝ)|^4727 ≤ (664730004951/2000000000000 : ℝ)^3703
        have hw : |(52742021/125000000 : ℝ)|=(52742021/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2283875649/5000000000 : ℝ)|^4727 ≤ (36778931107809/100000000000000 : ℝ)^3703
        have hw : |(2283875649/5000000000 : ℝ)|=(2283875649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3892389801/10000000000 : ℝ)|^4727 ≤ (7496142156111/25000000000000 : ℝ)^3703
        have hw : |(3892389801/10000000000 : ℝ)|=(3892389801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (519/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4089/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1637/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1637/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1637/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1637/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1637/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1637/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10367/100000 : ℝ) ^ (4723/1024 : ℝ) ≤ (2883315537251873/100000000000000000000 : ℝ) := by
    have hpowers : (10367/100000 : ℝ)^4723 ≤ (2883315537251873/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10367 : ℕ)^4723*100000000000000000000^1024 ≤ 2883315537251873^1024*100000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10367 100000 2883315537251873 100000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10367/100000 : ℝ)) (X := (2883315537251873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1637/10000 : ℝ) ^ (4723/1024 : ℝ) ≤ (5927793259496117/25000000000000000000 : ℝ) := by
    have hpowers : (1637/10000 : ℝ)^4723 ≤ (5927793259496117/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1637 : ℕ)^4723*25000000000000000000^1024 ≤ 5927793259496117^1024*10000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1637 10000 5927793259496117 25000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1637/10000 : ℝ)) (X := (5927793259496117/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002883315537251873/50000000000000000000 : ℝ) ≤ (10000125024282843/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (50002883315537251873/50000000000000000000 : ℝ)^1024 ≤ (10000125024282843/10000000000000000 : ℝ)^4723 := by
      have hnat : (50002883315537251873 : ℕ)^1024*10000000000000000^4723 ≤ 10000125024282843^4723*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002883315537251873 50000000000000000000 10000125024282843 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000125024282843/10000000000000000 : ℝ)) (X := (50002883315537251873/50000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026594488575236341/100000000000000000000 : ℝ) ≤ (5000288269327353/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (100026594488575236341/100000000000000000000 : ℝ)^1024 ≤ (5000288269327353/5000000000000000 : ℝ)^4723 := by
      have hnat : (100026594488575236341 : ℕ)^1024*5000000000000000^4723 ≤ 5000288269327353^4723*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026594488575236341 100000000000000000000 5000288269327353 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000288269327353/5000000000000000 : ℝ)) (X := (100026594488575236341/100000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505927793259496117/12500000000000000000 : ℝ) ≤ (10001028053026569/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (12505927793259496117/12500000000000000000 : ℝ)^1024 ≤ (10001028053026569/10000000000000000 : ℝ)^4723 := by
      have hnat : (12505927793259496117 : ℕ)^1024*10000000000000000^4723 ≤ 10001028053026569^4723*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505927793259496117 12500000000000000000 10001028053026569 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001028053026569/10000000000000000 : ℝ)) (X := (12505927793259496117/12500000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2883315537251873/100000000000000000000 : ℝ) ≤ ((20007129607261233029/20010000000000000000 : ℝ)+2*(150504790621/200100000000000 : ℝ)*(10367/100000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (20007129607261233029/20010000000000000000 : ℝ)+2*(150504790621/200100000000000 : ℝ)*(10367/100000 : ℝ)=(10000125024282843/10000000000000000 : ℝ) by norm_num, show 1+2*(2883315537251873/100000000000000000000 : ℝ)=(50002883315537251873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5927793259496117/25000000000000000000 : ℝ)+(2883315537251873/100000000000000000000 : ℝ) ≤ ((20007129607261233029/20010000000000000000 : ℝ)+(150504790621/200100000000000 : ℝ)*((1637/10000 : ℝ)+(10367/100000 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (20007129607261233029/20010000000000000000 : ℝ)+(150504790621/200100000000000 : ℝ)*((1637/10000 : ℝ)+(10367/100000 : ℝ))=(5000288269327353/5000000000000000 : ℝ) by norm_num, show 1+(5927793259496117/25000000000000000000 : ℝ)+(2883315537251873/100000000000000000000 : ℝ)=(100026594488575236341/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5927793259496117/25000000000000000000 : ℝ) ≤ ((20007129607261233029/20010000000000000000 : ℝ)+2*(150504790621/200100000000000 : ℝ)*(1637/10000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (20007129607261233029/20010000000000000000 : ℝ)+2*(150504790621/200100000000000 : ℝ)*(1637/10000 : ℝ)=(10001028053026569/10000000000000000 : ℝ) by norm_num, show 1+2*(5927793259496117/25000000000000000000 : ℝ)=(12505927793259496117/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20007129607261233029/20010000000000000000 : ℝ)*(X 1 0+X 2 0)+(150504790621/200100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (20007129607261233029/20010000000000000000 : ℝ)) (alpha := (150504790621/200100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20007129607261233029/20010000000000000000 : ℝ)*(X 0 1+X 2 1)+(150504790621/200100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (20007129607261233029/20010000000000000000 : ℝ)) (alpha := (150504790621/200100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20007129607261233029/20010000000000000000 : ℝ)*(X 0 2+X 1 2)+(150504790621/200100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (10367/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (20007129607261233029/20010000000000000000 : ℝ)) (alpha := (150504790621/200100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431155647/2500000000 : ℝ)*X 0 0+(1092387093/2000000000 : ℝ)*X 0 1+(517997911/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354692391/10000000000 : ℝ)*X 1 0+(-935032857/5000000000 : ℝ)*X 1 1+(1294994777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535469239/1000000000 : ℝ)*X 2 0+(5179979109/10000000000 : ℝ)*X 2 1+(-1870065713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4219187481/10000000000 : ℝ)*X 0 0+(3887258891/10000000000 : ℝ)*X 0 1+(914565777/2000000000 : ℝ)*X 0 2+(4219187481/10000000000 : ℝ)*X 1 0+(3887258891/10000000000 : ℝ)*X 1 1+(914565777/2000000000 : ℝ)*X 1 2+(4219187481/10000000000 : ℝ)*X 2 0+(3887258891/10000000000 : ℝ)*X 2 1+(914565777/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215586779/1250000000 : ℝ)*X 0 0+(5182067383/10000000000 : ℝ)*X 0 1+(5459825261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659990463/1250000000 : ℝ)*X 1 0+(-1590219561/10000000000 : ℝ)*X 1 1+(5459825261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659990463/1250000000 : ℝ)*X 2 0+(5459825261/10000000000 : ℝ)*X 2 1+(-1590219561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52742021/125000000 : ℝ)*X 0 0+(2283875649/5000000000 : ℝ)*X 0 1+(3892389801/10000000000 : ℝ)*X 0 2+(52742021/125000000 : ℝ)*X 1 0+(2283875649/5000000000 : ℝ)*X 1 1+(3892389801/10000000000 : ℝ)*X 1 2+(52742021/125000000 : ℝ)*X 2 0+(2283875649/5000000000 : ℝ)*X 2 1+(3892389801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1920414898491771218961935491/166750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1916865781/100000000000000 : ℝ)*(base19) + (1791782149/100000000000000 : ℝ)*(base23) + (66623767/100000000000000 : ℝ)*(lower2) + (285695297/100000000000000 : ℝ)*(upper3) + (6085629/3125000000000 : ℝ)*(upper5) + (1251338598480707/50000000000000 : ℝ)*(major0) + (1251338598480707/50000000000000 : ℝ)*(major1) + (1251338598480707/50000000000000 : ℝ)*(major2) + (1773335873039017/50000000000000 : ℝ)*(sp0) + (886673152652757/25000000000000 : ℝ)*(sp1) + (177334636784733/5000000000000 : ℝ)*(sp2) + (1458649304315203/100000000000000 : ℝ)*(sp3) + (2847674847/12500000000000 : ℝ)*(sp4) + (1017823977/10000000000000 : ℝ)*(sp7) + (729329741277487/50000000000000 : ℝ)*(f.failure) + (354669452747681/10000000000000 : ℝ)*(f.sum) + (18830763568001/10005000000000000000000000000 : ℝ)*base66 + (2213579170872290501/333500000000000000000000000000000 : ℝ)*base67 + (116486365147290501/333500000000000000000000000000000 : ℝ)*base69 + (3711249351732290501/333500000000000000000000000000000 : ℝ)*base71 + (13301773451389/10005000000000000000000000000 : ℝ)*base73 + (4957154573689290501/333500000000000000000000000000000 : ℝ)*base75 + (451837309490290501/333500000000000000000000000000000 : ℝ)*base77 + (8011457020385290501/333500000000000000000000000000000 : ℝ)*base79 + (1770165488869/10005000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (32213373/5000000000000000000000 : ℝ)*base89 + (32213373/5000000000000000000000 : ℝ)*base91 + (32213373/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1045642071299408751491149209/83375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (310339/16000000000 : ℝ)*(base19) + (262530547/12500000000000 : ℝ)*(base23) + (24685191/4000000000000 : ℝ)*(lower1) + (263491031/100000000000000 : ℝ)*(upper3) + (18066801/25000000000000 : ℝ)*(lower4) + (26001573/10000000000000 : ℝ)*(upper5) + (635114269086421/25000000000000 : ℝ)*(major0) + (635114269086421/25000000000000 : ℝ)*(major1) + (635114269086421/25000000000000 : ℝ)*(major2) + (1677426927/100000000000000 : ℝ)*(sp2) + (1800117320348903/50000000000000 : ℝ)*(sp4) + (225014543817441/6250000000000 : ℝ)*(sp5) + (1800115431513251/50000000000000 : ℝ)*(sp6) + (5922716375783/400000000000 : ℝ)*(sp7) + (5922716375783/400000000000 : ℝ)*(f.failure) + (1800117320348903/50000000000000 : ℝ)*(f.sum) + (11432689731181/2501250000000000000000000000 : ℝ)*base65 + (1094240965244933597/166750000000000000000000000000000 : ℝ)*base68 + (727529020571433597/166750000000000000000000000000000 : ℝ)*base70 + (903205199430433597/166750000000000000000000000000000 : ℝ)*base72 + (1014164855543/1250625000000000000000000000 : ℝ)*base73 + (599674874741066403/166750000000000000000000000000000 : ℝ)*base75 + (476543411110066403/166750000000000000000000000000000 : ℝ)*base77 + (1166589349192183597/166750000000000000000000000000000 : ℝ)*base80 + (28980076078879/10005000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (206043/40000000000000000000 : ℝ)*base90 + (206043/40000000000000000000 : ℝ)*base92 + (206043/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1602_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (519/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1602_s5_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1724634119/10000000000 : ℝ)*x 0 + (5461874763/10000000000 : ℝ)*x 1 + (5180032201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1724634119/10000000000 : ℝ)^4727 ≤ (2651910462591/25000000000000 : ℝ)^3703 := by
    have hnat : (1724634119 : ℕ)^4727*25000000000000^3703 ≤ 2651910462591^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724634119 10000000000 2651910462591 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461874763/10000000000 : ℝ)^4727 ≤ (2887940215647/6250000000000 : ℝ)^3703 := by
    have hnat : (5461874763 : ℕ)^4727*6250000000000^3703 ≤ 2887940215647^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461874763 10000000000 2887940215647 6250000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180032201/10000000000 : ℝ)^4727 ≤ (1727412587373/4000000000000 : ℝ)^3703 := by
    have hnat : (5180032201 : ℕ)^4727*4000000000000^3703 ≤ 1727412587373^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180032201 10000000000 1727412587373 4000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1724634119/10000000000 : ℝ), (5461874763/10000000000 : ℝ), (5180032201/10000000000 : ℝ)] ![(2651910462591/25000000000000 : ℝ), (2887940215647/6250000000000 : ℝ), (1727412587373/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1724634119/10000000000 : ℝ)|^4727 ≤ (2651910462591/25000000000000 : ℝ)^3703
        have hw : |(-1724634119/10000000000 : ℝ)|=(1724634119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461874763/10000000000 : ℝ)|^4727 ≤ (2887940215647/6250000000000 : ℝ)^3703
        have hw : |(5461874763/10000000000 : ℝ)|=(5461874763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180032201/10000000000 : ℝ)|^4727 ≤ (1727412587373/4000000000000 : ℝ)^3703
        have hw : |(5180032201/10000000000 : ℝ)|=(5180032201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677338219/5000000000 : ℝ)*x 0 + (-233752133/1250000000 : ℝ)*x 1 + (647503989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677338219/5000000000 : ℝ)^4727 ≤ (45052525889821/100000000000000 : ℝ)^3703 := by
    have hnat : (2677338219 : ℕ)^4727*100000000000000^3703 ≤ 45052525889821^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677338219 5000000000 45052525889821 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233752133/1250000000 : ℝ)^4727 ≤ (1470270310403/12500000000000 : ℝ)^3703 := by
    have hnat : (233752133 : ℕ)^4727*12500000000000^3703 ≤ 1470270310403^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233752133 1250000000 1470270310403 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647503989/1250000000 : ℝ)^4727 ≤ (43185311608701/100000000000000 : ℝ)^3703 := by
    have hnat : (647503989 : ℕ)^4727*100000000000000^3703 ≤ 43185311608701^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647503989 1250000000 43185311608701 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677338219/5000000000 : ℝ), (-233752133/1250000000 : ℝ), (647503989/1250000000 : ℝ)] ![(45052525889821/100000000000000 : ℝ), (1470270310403/12500000000000 : ℝ), (43185311608701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677338219/5000000000 : ℝ)|^4727 ≤ (45052525889821/100000000000000 : ℝ)^3703
        have hw : |(2677338219/5000000000 : ℝ)|=(2677338219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233752133/1250000000 : ℝ)|^4727 ≤ (1470270310403/12500000000000 : ℝ)^3703
        have hw : |(-233752133/1250000000 : ℝ)|=(233752133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647503989/1250000000 : ℝ)|^4727 ≤ (43185311608701/100000000000000 : ℝ)^3703
        have hw : |(647503989/1250000000 : ℝ)|=(647503989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354676491/10000000000 : ℝ)*x 0 + (518003199/1000000000 : ℝ)*x 1 + (-187001689/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354676491/10000000000 : ℝ)^4727 ≤ (45052526459059/100000000000000 : ℝ)^3703 := by
    have hnat : (5354676491 : ℕ)^4727*100000000000000^3703 ≤ 45052526459059^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354676491 10000000000 45052526459059 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518003199/1000000000 : ℝ)^4727 ≤ (107963281097/250000000000 : ℝ)^3703 := by
    have hnat : (518003199 : ℕ)^4727*250000000000^3703 ≤ 107963281097^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518003199 1000000000 107963281097 250000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187001689/1000000000 : ℝ)^4727 ≤ (588108054307/5000000000000 : ℝ)^3703 := by
    have hnat : (187001689 : ℕ)^4727*5000000000000^3703 ≤ 588108054307^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187001689 1000000000 588108054307 5000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354676491/10000000000 : ℝ), (518003199/1000000000 : ℝ), (-187001689/1000000000 : ℝ)] ![(45052526459059/100000000000000 : ℝ), (107963281097/250000000000 : ℝ), (588108054307/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354676491/10000000000 : ℝ)|^4727 ≤ (45052526459059/100000000000000 : ℝ)^3703
        have hw : |(5354676491/10000000000 : ℝ)|=(5354676491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518003199/1000000000 : ℝ)|^4727 ≤ (107963281097/250000000000 : ℝ)^3703
        have hw : |(518003199/1000000000 : ℝ)|=(518003199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187001689/1000000000 : ℝ)|^4727 ≤ (588108054307/5000000000000 : ℝ)^3703
        have hw : |(-187001689/1000000000 : ℝ)|=(187001689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219195461/10000000000 : ℝ)*x 0 + (1943698137/5000000000 : ℝ)*x 1 + (4572689731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219195461/10000000000 : ℝ)^4727 ≤ (16617414426999/50000000000000 : ℝ)^3703 := by
    have hnat : (4219195461 : ℕ)^4727*50000000000000^3703 ≤ 16617414426999^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219195461 10000000000 16617414426999 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943698137/5000000000 : ℝ)^4727 ≤ (29935472896279/100000000000000 : ℝ)^3703 := by
    have hnat : (1943698137 : ℕ)^4727*100000000000000^3703 ≤ 29935472896279^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943698137 5000000000 29935472896279 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572689731/10000000000 : ℝ)^4727 ≤ (36829698237483/100000000000000 : ℝ)^3703 := by
    have hnat : (4572689731 : ℕ)^4727*100000000000000^3703 ≤ 36829698237483^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572689731 10000000000 36829698237483 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219195461/10000000000 : ℝ), (1943698137/5000000000 : ℝ), (4572689731/10000000000 : ℝ)] ![(16617414426999/50000000000000 : ℝ), (29935472896279/100000000000000 : ℝ), (36829698237483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219195461/10000000000 : ℝ)|^4727 ≤ (16617414426999/50000000000000 : ℝ)^3703
        have hw : |(4219195461/10000000000 : ℝ)|=(4219195461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1943698137/5000000000 : ℝ)|^4727 ≤ (29935472896279/100000000000000 : ℝ)^3703
        have hw : |(1943698137/5000000000 : ℝ)|=(1943698137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572689731/10000000000 : ℝ)|^4727 ≤ (36829698237483/100000000000000 : ℝ)^3703
        have hw : |(4572689731/10000000000 : ℝ)|=(4572689731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431176469/2500000000 : ℝ)*x 0 + (1295529663/2500000000 : ℝ)*x 1 + (5459766261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431176469/2500000000 : ℝ)^4727 ≤ (10608205255157/100000000000000 : ℝ)^3703 := by
    have hnat : (431176469 : ℕ)^4727*100000000000000^3703 ≤ 10608205255157^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431176469 2500000000 10608205255157 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295529663/2500000000 : ℝ)^4727 ≤ (4320752055943/10000000000000 : ℝ)^3703 := by
    have hnat : (1295529663 : ℕ)^4727*10000000000000^3703 ≤ 4320752055943^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295529663 2500000000 4320752055943 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459766261/10000000000 : ℝ)^4727 ≤ (23092137088603/50000000000000 : ℝ)^3703 := by
    have hnat : (5459766261 : ℕ)^4727*50000000000000^3703 ≤ 23092137088603^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459766261 10000000000 23092137088603 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431176469/2500000000 : ℝ), (1295529663/2500000000 : ℝ), (5459766261/10000000000 : ℝ)] ![(10608205255157/100000000000000 : ℝ), (4320752055943/10000000000000 : ℝ), (23092137088603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431176469/2500000000 : ℝ)|^4727 ≤ (10608205255157/100000000000000 : ℝ)^3703
        have hw : |(-431176469/2500000000 : ℝ)|=(431176469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295529663/2500000000 : ℝ)|^4727 ≤ (4320752055943/10000000000000 : ℝ)^3703
        have hw : |(1295529663/2500000000 : ℝ)|=(1295529663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459766261/10000000000 : ℝ)|^4727 ≤ (23092137088603/50000000000000 : ℝ)^3703
        have hw : |(5459766261/10000000000 : ℝ)|=(5459766261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279937689/10000000000 : ℝ)*x 0 + (-1590282973/10000000000 : ℝ)*x 1 + (5459766319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279937689/10000000000 : ℝ)^4727 ≤ (44251361127929/100000000000000 : ℝ)^3703 := by
    have hnat : (5279937689 : ℕ)^4727*100000000000000^3703 ≤ 44251361127929^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279937689 10000000000 44251361127929 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590282973/10000000000 : ℝ)^4727 ≤ (9564364044913/100000000000000 : ℝ)^3703 := by
    have hnat : (1590282973 : ℕ)^4727*100000000000000^3703 ≤ 9564364044913^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590282973 10000000000 9564364044913 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459766319/10000000000 : ℝ)^4727 ≤ (23092137401751/50000000000000 : ℝ)^3703 := by
    have hnat : (5459766319 : ℕ)^4727*50000000000000^3703 ≤ 23092137401751^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459766319 10000000000 23092137401751 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279937689/10000000000 : ℝ), (-1590282973/10000000000 : ℝ), (5459766319/10000000000 : ℝ)] ![(44251361127929/100000000000000 : ℝ), (9564364044913/100000000000000 : ℝ), (23092137401751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279937689/10000000000 : ℝ)|^4727 ≤ (44251361127929/100000000000000 : ℝ)^3703
        have hw : |(5279937689/10000000000 : ℝ)|=(5279937689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590282973/10000000000 : ℝ)|^4727 ≤ (9564364044913/100000000000000 : ℝ)^3703
        have hw : |(-1590282973/10000000000 : ℝ)|=(1590282973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459766319/10000000000 : ℝ)|^4727 ≤ (23092137401751/50000000000000 : ℝ)^3703
        have hw : |(5459766319/10000000000 : ℝ)|=(5459766319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659992223/1250000000 : ℝ)*x 0 + (5459766361/10000000000 : ℝ)*x 1 + (-1590282783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659992223/1250000000 : ℝ)^4727 ≤ (44251362144303/100000000000000 : ℝ)^3703 := by
    have hnat : (659992223 : ℕ)^4727*100000000000000^3703 ≤ 44251362144303^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659992223 1250000000 44251362144303 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459766361/10000000000 : ℝ)^4727 ≤ (46184275257027/100000000000000 : ℝ)^3703 := by
    have hnat : (5459766361 : ℕ)^4727*100000000000000^3703 ≤ 46184275257027^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459766361 10000000000 46184275257027 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1590282783/10000000000 : ℝ)^4727 ≤ (9564362586209/100000000000000 : ℝ)^3703 := by
    have hnat : (1590282783 : ℕ)^4727*100000000000000^3703 ≤ 9564362586209^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590282783 10000000000 9564362586209 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659992223/1250000000 : ℝ), (5459766361/10000000000 : ℝ), (-1590282783/10000000000 : ℝ)] ![(44251362144303/100000000000000 : ℝ), (46184275257027/100000000000000 : ℝ), (9564362586209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659992223/1250000000 : ℝ)|^4727 ≤ (44251362144303/100000000000000 : ℝ)^3703
        have hw : |(659992223/1250000000 : ℝ)|=(659992223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459766361/10000000000 : ℝ)|^4727 ≤ (46184275257027/100000000000000 : ℝ)^3703
        have hw : |(5459766361/10000000000 : ℝ)|=(5459766361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1590282783/10000000000 : ℝ)|^4727 ≤ (9564362586209/100000000000000 : ℝ)^3703
        have hw : |(-1590282783/10000000000 : ℝ)|=(1590282783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s5_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219369503/10000000000 : ℝ)*x 0 + (4567616433/10000000000 : ℝ)*x 1 + (243282673/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219369503/10000000000 : ℝ)^4727 ≤ (33236578911159/100000000000000 : ℝ)^3703 := by
    have hnat : (4219369503 : ℕ)^4727*100000000000000^3703 ≤ 33236578911159^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219369503 10000000000 33236578911159 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4567616433/10000000000 : ℝ)^4727 ≤ (4597193113423/12500000000000 : ℝ)^3703 := by
    have hnat : (4567616433 : ℕ)^4727*12500000000000^3703 ≤ 4597193113423^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567616433 10000000000 4597193113423 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243282673/625000000 : ℝ)^4727 ≤ (7496469044353/25000000000000 : ℝ)^3703 := by
    have hnat : (243282673 : ℕ)^4727*25000000000000^3703 ≤ 7496469044353^3703*625000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243282673 625000000 7496469044353 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219369503/10000000000 : ℝ), (4567616433/10000000000 : ℝ), (243282673/625000000 : ℝ)] ![(33236578911159/100000000000000 : ℝ), (4597193113423/12500000000000 : ℝ), (7496469044353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219369503/10000000000 : ℝ)|^4727 ≤ (33236578911159/100000000000000 : ℝ)^3703
        have hw : |(4219369503/10000000000 : ℝ)|=(4219369503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4567616433/10000000000 : ℝ)|^4727 ≤ (4597193113423/12500000000000 : ℝ)^3703
        have hw : |(4567616433/10000000000 : ℝ)|=(4567616433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243282673/625000000 : ℝ)|^4727 ≤ (7496469044353/25000000000000 : ℝ)^3703
        have hw : |(243282673/625000000 : ℝ)|=(243282673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5191/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8177/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (519/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (519/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (519/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4089/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (519/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (519/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4089/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (519/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (519/5000 : ℝ) ^ (4723/1024 : ℝ) ≤ (145001483791299/5000000000000000000 : ℝ) := by
    have hpowers : (519/5000 : ℝ)^4723 ≤ (145001483791299/5000000000000000000 : ℝ)^1024 := by
      have hnat : (519 : ℕ)^4723*5000000000000000000^1024 ≤ 145001483791299^1024*5000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        519 5000 145001483791299 5000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (519/5000 : ℝ)) (X := (145001483791299/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4089/25000 : ℝ) ^ (4723/1024 : ℝ) ≤ (11808893760430977/50000000000000000000 : ℝ) := by
    have hpowers : (4089/25000 : ℝ)^4723 ≤ (11808893760430977/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4089 : ℕ)^4723*50000000000000000000^1024 ≤ 11808893760430977^1024*25000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4089 25000 11808893760430977 50000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4089/25000 : ℝ)) (X := (11808893760430977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500145001483791299/2500000000000000000 : ℝ) ≤ (5000062874506501/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (2500145001483791299/2500000000000000000 : ℝ)^1024 ≤ (5000062874506501/5000000000000000 : ℝ)^4723 := by
      have hnat : (2500145001483791299 : ℕ)^1024*5000000000000000^4723 ≤ 5000062874506501^4723*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500145001483791299 2500000000000000000 5000062874506501 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000062874506501/5000000000000000 : ℝ)) (X := (2500145001483791299/2500000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013258908598343967/50000000000000000000 : ℝ) ≤ (10000574876677863/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (50013258908598343967/50000000000000000000 : ℝ)^1024 ≤ (10000574876677863/10000000000000000 : ℝ)^4723 := by
      have hnat : (50013258908598343967 : ℕ)^1024*10000000000000000^4723 ≤ 10000574876677863^4723*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013258908598343967 50000000000000000000 10000574876677863 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000574876677863/10000000000000000 : ℝ)) (X := (50013258908598343967/50000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011808893760430977/25000000000000000000 : ℝ) ≤ (2500256001085681/2500000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (25011808893760430977/25000000000000000000 : ℝ)^1024 ≤ (2500256001085681/2500000000000000 : ℝ)^4723 := by
      have hnat : (25011808893760430977 : ℕ)^1024*2500000000000000^4723 ≤ 2500256001085681^4723*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011808893760430977 25000000000000000000 2500256001085681 2500000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500256001085681/2500000000000000 : ℝ)) (X := (25011808893760430977/25000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(145001483791299/5000000000000000000 : ℝ) ≤ ((2489642816074132733/2490000000000000000 : ℝ)+2*(449127664861/597600000000000 : ℝ)*(519/5000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (2489642816074132733/2490000000000000000 : ℝ)+2*(449127664861/597600000000000 : ℝ)*(519/5000 : ℝ)=(5000062874506501/5000000000000000 : ℝ) by norm_num, show 1+2*(145001483791299/5000000000000000000 : ℝ)=(2500145001483791299/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11808893760430977/50000000000000000000 : ℝ)+(145001483791299/5000000000000000000 : ℝ) ≤ ((2489642816074132733/2490000000000000000 : ℝ)+(449127664861/597600000000000 : ℝ)*((4089/25000 : ℝ)+(519/5000 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (2489642816074132733/2490000000000000000 : ℝ)+(449127664861/597600000000000 : ℝ)*((4089/25000 : ℝ)+(519/5000 : ℝ))=(10000574876677863/10000000000000000 : ℝ) by norm_num, show 1+(11808893760430977/50000000000000000000 : ℝ)+(145001483791299/5000000000000000000 : ℝ)=(50013258908598343967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11808893760430977/50000000000000000000 : ℝ) ≤ ((2489642816074132733/2490000000000000000 : ℝ)+2*(449127664861/597600000000000 : ℝ)*(4089/25000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (2489642816074132733/2490000000000000000 : ℝ)+2*(449127664861/597600000000000 : ℝ)*(4089/25000 : ℝ)=(2500256001085681/2500000000000000 : ℝ) by norm_num, show 1+2*(11808893760430977/50000000000000000000 : ℝ)=(25011808893760430977/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2489642816074132733/2490000000000000000 : ℝ)*(X 1 0+X 2 0)+(449127664861/597600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (519/5000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (2489642816074132733/2490000000000000000 : ℝ)) (alpha := (449127664861/597600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2489642816074132733/2490000000000000000 : ℝ)*(X 0 1+X 2 1)+(449127664861/597600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (519/5000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (2489642816074132733/2490000000000000000 : ℝ)) (alpha := (449127664861/597600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2489642816074132733/2490000000000000000 : ℝ)*(X 0 2+X 1 2)+(449127664861/597600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (519/5000 : ℝ)) (hi := (4089/25000 : ℝ)) (c := (2489642816074132733/2490000000000000000 : ℝ)) (alpha := (449127664861/597600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1724634119/10000000000 : ℝ)*X 0 0+(5461874763/10000000000 : ℝ)*X 0 1+(5180032201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677338219/5000000000 : ℝ)*X 1 0+(-233752133/1250000000 : ℝ)*X 1 1+(647503989/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354676491/10000000000 : ℝ)*X 2 0+(518003199/1000000000 : ℝ)*X 2 1+(-187001689/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4219195461/10000000000 : ℝ)*X 0 0+(1943698137/5000000000 : ℝ)*X 0 1+(4572689731/10000000000 : ℝ)*X 0 2+(4219195461/10000000000 : ℝ)*X 1 0+(1943698137/5000000000 : ℝ)*X 1 1+(4572689731/10000000000 : ℝ)*X 1 2+(4219195461/10000000000 : ℝ)*X 2 0+(1943698137/5000000000 : ℝ)*X 2 1+(4572689731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431176469/2500000000 : ℝ)*X 0 0+(1295529663/2500000000 : ℝ)*X 0 1+(5459766261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279937689/10000000000 : ℝ)*X 1 0+(-1590282973/10000000000 : ℝ)*X 1 1+(5459766319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659992223/1250000000 : ℝ)*X 2 0+(5459766361/10000000000 : ℝ)*X 2 1+(-1590282783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4219369503/10000000000 : ℝ)*X 0 0+(4567616433/10000000000 : ℝ)*X 0 1+(243282673/625000000 : ℝ)*X 0 2+(4219369503/10000000000 : ℝ)*X 1 0+(4567616433/10000000000 : ℝ)*X 1 1+(243282673/625000000 : ℝ)*X 1 2+(4219369503/10000000000 : ℝ)*X 2 0+(4567616433/10000000000 : ℝ)*X 2 1+(243282673/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294635647998281365528591511/124500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239110777/50000000000000 : ℝ)*(base19) + (191922963/50000000000000 : ℝ)*(base23) + (1386799/2000000000000 : ℝ)*(lower2) + (6852663/50000000000000 : ℝ)*(upper3) + (53722657/100000000000000 : ℝ)*(upper5) + (2503659001850789/100000000000000 : ℝ)*(major0) + (2503659001850789/100000000000000 : ℝ)*(major1) + (250365900185079/10000000000000 : ℝ)*(major2) + (887020530747851/25000000000000 : ℝ)*(sp0) + (709617145845871/20000000000000 : ℝ)*(sp1) + (1774042911802491/50000000000000 : ℝ)*(sp2) + (91201890961217/6250000000000 : ℝ)*(sp3) + (816891901/20000000000000 : ℝ)*(sp4) + (730993073/50000000000000 : ℝ)*(sp7) + (729615858682809/50000000000000 : ℝ)*(f.failure) + (3548086207450909/100000000000000 : ℝ)*(f.sum) + (178740606293279/59760000000000000000000000000 : ℝ)*base65 + (1387243206686098663/249000000000000000000000000000000 : ℝ)*base68 + (310662810743633971/74700000000000000000000000000000 : ℝ)*base69 + (537747451724098663/249000000000000000000000000000000 : ℝ)*base72 + (220509574446241/59760000000000000000000000000 : ℝ)*base74 + (815904005856066029/74700000000000000000000000000000 : ℝ)*base76 + (2213671367032941511/747000000000000000000000000000000 : ℝ)*base77 + (2755999017865058489/747000000000000000000000000000000 : ℝ)*base80 + (5367878406929/29880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (52465211/5000000000000000000000 : ℝ)*base89 + (52465211/5000000000000000000000 : ℝ)*base91 + (2465211/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148350064557104590628541979/31125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70017539/12500000000000 : ℝ)*(base19) + (715159461/100000000000000 : ℝ)*(base23) + (16425493/12500000000000 : ℝ)*(lower1) + (71901303/50000000000000 : ℝ)*(upper3) + (3956989/20000000000000 : ℝ)*(lower4) + (1650597/1562500000000 : ℝ)*(upper5) + (1270739223278971/50000000000000 : ℝ)*(major0) + (1270739223278971/50000000000000 : ℝ)*(major1) + (1270739223278971/50000000000000 : ℝ)*(major2) + (745215577/20000000000000 : ℝ)*(sp2) + (3601682345245267/100000000000000 : ℝ)*(sp4) + (720336357020991/20000000000000 : ℝ)*(sp5) + (1800838952003961/50000000000000 : ℝ)*(sp6) + (370318597248759/25000000000000 : ℝ)*(sp7) + (370318597248759/25000000000000 : ℝ)*(f.failure) + (3601682345245267/100000000000000 : ℝ)*(f.sum) + (29310034409009/14940000000000000000000000000 : ℝ)*base66 + (1648058360241639271/373500000000000000000000000000000 : ℝ)*base68 + (4882519679372139271/373500000000000000000000000000000 : ℝ)*base70 + (4734322262720139271/373500000000000000000000000000000 : ℝ)*base72 + (48767942065411/14940000000000000000000000000 : ℝ)*base73 + (102781297314860729/373500000000000000000000000000000 : ℝ)*base75 + (7021067567138139271/373500000000000000000000000000000 : ℝ)*base78 + (5199756851379639271/373500000000000000000000000000000 : ℝ)*base80 + (93936048562351/14940000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (34690261/2500000000000000000000 : ℝ)*base89 + (34690261/2500000000000000000000 : ℝ)*base91 + (34690261/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1602_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (519/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1602_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1602_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1602_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1602_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1602_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
