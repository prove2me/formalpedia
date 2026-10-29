-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:06.845206+00:00
-- url     : https://prove2.me/submissions/cf23a35e-376c-4055-9922-e5b7f34c9508

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
theorem support_rectangle_w1433_s3_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-983428793/5000000000 : ℝ)*x 0 + (5416875403/10000000000 : ℝ)*x 1 + (5238812471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983428793/5000000000 : ℝ)^4393 ≤ (11998218741971/100000000000000 : ℝ)^3369 := by
    have hnat : (983428793 : ℕ)^4393*100000000000000^3369 ≤ 11998218741971^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983428793 5000000000 11998218741971 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416875403/10000000000 : ℝ)^4393 ≤ (22479798239419/50000000000000 : ℝ)^3369 := by
    have hnat : (5416875403 : ℕ)^4393*50000000000000^3369 ≤ 22479798239419^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416875403 10000000000 22479798239419 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238812471/10000000000 : ℝ)^4393 ≤ (43042184767199/100000000000000 : ℝ)^3369 := by
    have hnat : (5238812471 : ℕ)^4393*100000000000000^3369 ≤ 43042184767199^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238812471 10000000000 43042184767199 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983428793/5000000000 : ℝ), (5416875403/10000000000 : ℝ), (5238812471/10000000000 : ℝ)] ![(11998218741971/100000000000000 : ℝ), (22479798239419/50000000000000 : ℝ), (43042184767199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983428793/5000000000 : ℝ)|^4393 ≤ (11998218741971/100000000000000 : ℝ)^3369
        have hw : |(-983428793/5000000000 : ℝ)|=(983428793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416875403/10000000000 : ℝ)|^4393 ≤ (22479798239419/50000000000000 : ℝ)^3369
        have hw : |(5416875403/10000000000 : ℝ)|=(5416875403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238812471/10000000000 : ℝ)|^4393 ≤ (43042184767199/100000000000000 : ℝ)^3369
        have hw : |(5238812471/10000000000 : ℝ)|=(5238812471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334345763/625000000 : ℝ)*x 0 + (-1028840201/5000000000 : ℝ)*x 1 + (523881239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334345763/625000000 : ℝ)^4393 ≤ (44232145435921/100000000000000 : ℝ)^3369 := by
    have hnat : (334345763 : ℕ)^4393*100000000000000^3369 ≤ 44232145435921^3369*625000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334345763 625000000 44232145435921 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028840201/5000000000 : ℝ)^4393 ≤ (12725670648817/100000000000000 : ℝ)^3369 := by
    have hnat : (1028840201 : ℕ)^4393*100000000000000^3369 ≤ 12725670648817^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028840201 5000000000 12725670648817 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523881239/1000000000 : ℝ)^4393 ≤ (1721687355977/4000000000000 : ℝ)^3369 := by
    have hnat : (523881239 : ℕ)^4393*4000000000000^3369 ≤ 1721687355977^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523881239 1000000000 1721687355977 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334345763/625000000 : ℝ), (-1028840201/5000000000 : ℝ), (523881239/1000000000 : ℝ)] ![(44232145435921/100000000000000 : ℝ), (12725670648817/100000000000000 : ℝ), (1721687355977/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334345763/625000000 : ℝ)|^4393 ≤ (44232145435921/100000000000000 : ℝ)^3369
        have hw : |(334345763/625000000 : ℝ)|=(334345763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028840201/5000000000 : ℝ)|^4393 ≤ (12725670648817/100000000000000 : ℝ)^3369
        have hw : |(-1028840201/5000000000 : ℝ)|=(1028840201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523881239/1000000000 : ℝ)|^4393 ≤ (1721687355977/4000000000000 : ℝ)^3369
        have hw : |(523881239/1000000000 : ℝ)|=(523881239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349532229/10000000000 : ℝ)*x 0 + (1309703071/2500000000 : ℝ)*x 1 + (-411536103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349532229/10000000000 : ℝ)^4393 ≤ (22116072831167/50000000000000 : ℝ)^3369 := by
    have hnat : (5349532229 : ℕ)^4393*50000000000000^3369 ≤ 22116072831167^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349532229 10000000000 22116072831167 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309703071/2500000000 : ℝ)^4393 ≤ (43042182763819/100000000000000 : ℝ)^3369 := by
    have hnat : (1309703071 : ℕ)^4393*100000000000000^3369 ≤ 43042182763819^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309703071 2500000000 43042182763819 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411536103/2000000000 : ℝ)^4393 ≤ (509026862403/4000000000000 : ℝ)^3369 := by
    have hnat : (411536103 : ℕ)^4393*4000000000000^3369 ≤ 509026862403^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411536103 2000000000 509026862403 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349532229/10000000000 : ℝ), (1309703071/2500000000 : ℝ), (-411536103/2000000000 : ℝ)] ![(22116072831167/50000000000000 : ℝ), (43042182763819/100000000000000 : ℝ), (509026862403/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349532229/10000000000 : ℝ)|^4393 ≤ (22116072831167/50000000000000 : ℝ)^3369
        have hw : |(5349532229/10000000000 : ℝ)|=(5349532229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309703071/2500000000 : ℝ)|^4393 ≤ (43042182763819/100000000000000 : ℝ)^3369
        have hw : |(1309703071/2500000000 : ℝ)|=(1309703071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411536103/2000000000 : ℝ)|^4393 ≤ (509026862403/4000000000000 : ℝ)^3369
        have hw : |(-411536103/2000000000 : ℝ)|=(411536103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075685801/2500000000 : ℝ)*x 0 + (10284343/25000000 : ℝ)*x 1 + (1124877731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075685801/2500000000 : ℝ)^4393 ≤ (33298385029089/100000000000000 : ℝ)^3369 := by
    have hnat : (1075685801 : ℕ)^4393*100000000000000^3369 ≤ 33298385029089^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075685801 2500000000 33298385029089 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10284343/25000000 : ℝ)^4393 ≤ (15701986888219/50000000000000 : ℝ)^3369 := by
    have hnat : (10284343 : ℕ)^4393*50000000000000^3369 ≤ 15701986888219^3369*25000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10284343 25000000 15701986888219 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124877731/2500000000 : ℝ)^4393 ≤ (7059528235907/20000000000000 : ℝ)^3369 := by
    have hnat : (1124877731 : ℕ)^4393*20000000000000^3369 ≤ 7059528235907^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124877731 2500000000 7059528235907 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075685801/2500000000 : ℝ), (10284343/25000000 : ℝ), (1124877731/2500000000 : ℝ)] ![(33298385029089/100000000000000 : ℝ), (15701986888219/50000000000000 : ℝ), (7059528235907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075685801/2500000000 : ℝ)|^4393 ≤ (33298385029089/100000000000000 : ℝ)^3369
        have hw : |(1075685801/2500000000 : ℝ)|=(1075685801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10284343/25000000 : ℝ)|^4393 ≤ (15701986888219/50000000000000 : ℝ)^3369
        have hw : |(10284343/25000000 : ℝ)|=(10284343/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124877731/2500000000 : ℝ)|^4393 ≤ (7059528235907/20000000000000 : ℝ)^3369
        have hw : |(1124877731/2500000000 : ℝ)|=(1124877731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966872479/10000000000 : ℝ)*x 0 + (261976127/500000000 : ℝ)*x 1 + (21156881/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966872479/10000000000 : ℝ)^4393 ≤ (11998337206067/100000000000000 : ℝ)^3369 := by
    have hnat : (1966872479 : ℕ)^4393*100000000000000^3369 ≤ 11998337206067^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966872479 10000000000 11998337206067 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261976127/500000000 : ℝ)^4393 ≤ (21524896038871/50000000000000 : ℝ)^3369 := by
    have hnat : (261976127 : ℕ)^4393*50000000000000^3369 ≤ 21524896038871^3369*500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261976127 500000000 21524896038871 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21156881/39062500 : ℝ)^4393 ≤ (44951870698453/100000000000000 : ℝ)^3369 := by
    have hnat : (21156881 : ℕ)^4393*100000000000000^3369 ≤ 44951870698453^3369*39062500^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21156881 39062500 44951870698453 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966872479/10000000000 : ℝ), (261976127/500000000 : ℝ), (21156881/39062500 : ℝ)] ![(11998337206067/100000000000000 : ℝ), (21524896038871/50000000000000 : ℝ), (44951870698453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966872479/10000000000 : ℝ)|^4393 ≤ (11998337206067/100000000000000 : ℝ)^3369
        have hw : |(-1966872479/10000000000 : ℝ)|=(1966872479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261976127/500000000 : ℝ)|^4393 ≤ (21524896038871/50000000000000 : ℝ)^3369
        have hw : |(261976127/500000000 : ℝ)|=(261976127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21156881/39062500 : ℝ)|^4393 ≤ (44951870698453/100000000000000 : ℝ)^3369
        have hw : |(21156881/39062500 : ℝ)|=(21156881/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325805829/2500000000 : ℝ)*x 0 + (-940165677/5000000000 : ℝ)*x 1 + (1354040373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325805829/2500000000 : ℝ)^4393 ≤ (43733520605437/100000000000000 : ℝ)^3369 := by
    have hnat : (1325805829 : ℕ)^4393*100000000000000^3369 ≤ 43733520605437^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325805829 2500000000 43733520605437 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940165677/5000000000 : ℝ)^4393 ≤ (11314609153499/100000000000000 : ℝ)^3369 := by
    have hnat : (940165677 : ℕ)^4393*100000000000000^3369 ≤ 11314609153499^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940165677 5000000000 11314609153499 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354040373/2500000000 : ℝ)^4393 ≤ (1798074808891/4000000000000 : ℝ)^3369 := by
    have hnat : (1354040373 : ℕ)^4393*4000000000000^3369 ≤ 1798074808891^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354040373 2500000000 1798074808891 4000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325805829/2500000000 : ℝ), (-940165677/5000000000 : ℝ), (1354040373/2500000000 : ℝ)] ![(43733520605437/100000000000000 : ℝ), (11314609153499/100000000000000 : ℝ), (1798074808891/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325805829/2500000000 : ℝ)|^4393 ≤ (43733520605437/100000000000000 : ℝ)^3369
        have hw : |(1325805829/2500000000 : ℝ)|=(1325805829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940165677/5000000000 : ℝ)|^4393 ≤ (11314609153499/100000000000000 : ℝ)^3369
        have hw : |(-940165677/5000000000 : ℝ)|=(940165677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354040373/2500000000 : ℝ)|^4393 ≤ (1798074808891/4000000000000 : ℝ)^3369
        have hw : |(1354040373/2500000000 : ℝ)|=(1354040373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303223001/10000000000 : ℝ)*x 0 + (169255057/312500000 : ℝ)*x 1 + (-1880331329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303223001/10000000000 : ℝ)^4393 ≤ (21866758609101/50000000000000 : ℝ)^3369 := by
    have hnat : (5303223001 : ℕ)^4393*50000000000000^3369 ≤ 21866758609101^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303223001 10000000000 21866758609101 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169255057/312500000 : ℝ)^4393 ≤ (11237968453813/25000000000000 : ℝ)^3369 := by
    have hnat : (169255057 : ℕ)^4393*25000000000000^3369 ≤ 11237968453813^3369*312500000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169255057 312500000 11237968453813 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1880331329/10000000000 : ℝ)^4393 ≤ (5657304478671/50000000000000 : ℝ)^3369 := by
    have hnat : (1880331329 : ℕ)^4393*50000000000000^3369 ≤ 5657304478671^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880331329 10000000000 5657304478671 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303223001/10000000000 : ℝ), (169255057/312500000 : ℝ), (-1880331329/10000000000 : ℝ)] ![(21866758609101/50000000000000 : ℝ), (11237968453813/25000000000000 : ℝ), (5657304478671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303223001/10000000000 : ℝ)|^4393 ≤ (21866758609101/50000000000000 : ℝ)^3369
        have hw : |(5303223001/10000000000 : ℝ)|=(5303223001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169255057/312500000 : ℝ)|^4393 ≤ (11237968453813/25000000000000 : ℝ)^3369
        have hw : |(169255057/312500000 : ℝ)|=(169255057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1880331329/10000000000 : ℝ)|^4393 ≤ (5657304478671/50000000000000 : ℝ)^3369
        have hw : |(-1880331329/10000000000 : ℝ)|=(1880331329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s3_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151387971/5000000000 : ℝ)*x 0 + (899594659/2000000000 : ℝ)*x 1 + (4115283939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151387971/5000000000 : ℝ)^4393 ≤ (16649357695733/50000000000000 : ℝ)^3369 := by
    have hnat : (2151387971 : ℕ)^4393*50000000000000^3369 ≤ 16649357695733^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151387971 5000000000 16649357695733 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899594659/2000000000 : ℝ)^4393 ≤ (17640956660943/50000000000000 : ℝ)^3369 := by
    have hnat : (899594659 : ℕ)^4393*50000000000000^3369 ≤ 17640956660943^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899594659 2000000000 17640956660943 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4115283939/10000000000 : ℝ)^4393 ≤ (31419371272571/100000000000000 : ℝ)^3369 := by
    have hnat : (4115283939 : ℕ)^4393*100000000000000^3369 ≤ 31419371272571^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115283939 10000000000 31419371272571 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151387971/5000000000 : ℝ), (899594659/2000000000 : ℝ), (4115283939/10000000000 : ℝ)] ![(16649357695733/50000000000000 : ℝ), (17640956660943/50000000000000 : ℝ), (31419371272571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151387971/5000000000 : ℝ)|^4393 ≤ (16649357695733/50000000000000 : ℝ)^3369
        have hw : |(2151387971/5000000000 : ℝ)|=(2151387971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899594659/2000000000 : ℝ)|^4393 ≤ (17640956660943/50000000000000 : ℝ)^3369
        have hw : |(899594659/2000000000 : ℝ)|=(899594659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4115283939/10000000000 : ℝ)|^4393 ≤ (31419371272571/100000000000000 : ℝ)^3369
        have hw : |(4115283939/10000000000 : ℝ)|=(4115283939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (467/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10389/100000 : ℝ) ^ (549/128 : ℝ) ≤ (6053733991500609/100000000000000000000 : ℝ) := by
    have hpowers : (10389/100000 : ℝ)^549 ≤ (6053733991500609/100000000000000000000 : ℝ)^128 := by
      have hnat : (10389 : ℕ)^549*100000000000000000000^128 ≤ 6053733991500609^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389 100000 6053733991500609 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10389/100000 : ℝ)) (X := (6053733991500609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (15787/100000 : ℝ) ^ (549/128 : ℝ) ≤ (36429810872959509/100000000000000000000 : ℝ) := by
    have hpowers : (15787/100000 : ℝ)^549 ≤ (36429810872959509/100000000000000000000 : ℝ)^128 := by
      have hnat : (15787 : ℕ)^549*100000000000000000000^128 ≤ 36429810872959509^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15787 100000 36429810872959509 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15787/100000 : ℝ)) (X := (36429810872959509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006053733991500609/50000000000000000000 : ℝ) ≤ (10000282273945839/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50006053733991500609/50000000000000000000 : ℝ)^128 ≤ (10000282273945839/10000000000000000 : ℝ)^549 := by
      have hnat : (50006053733991500609 : ℕ)^128*10000000000000000^549 ≤ 10000282273945839^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006053733991500609 50000000000000000000 10000282273945839 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282273945839/10000000000000000 : ℝ)) (X := (50006053733991500609/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021241772432230059/50000000000000000000 : ℝ) ≤ (10000990347572551/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50021241772432230059/50000000000000000000 : ℝ)^128 ≤ (10000990347572551/10000000000000000 : ℝ)^549 := by
      have hnat : (50021241772432230059 : ℕ)^128*10000000000000000^549 ≤ 10000990347572551^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021241772432230059 50000000000000000000 10000990347572551 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000990347572551/10000000000000000 : ℝ)) (X := (50021241772432230059/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036429810872959509/50000000000000000000 : ℝ) ≤ (10001698421199263/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50036429810872959509/50000000000000000000 : ℝ)^128 ≤ (10001698421199263/10000000000000000 : ℝ)^549 := by
      have hnat : (50036429810872959509 : ℕ)^128*10000000000000000^549 ≤ 10001698421199263^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036429810872959509 50000000000000000000 10001698421199263 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001698421199263/10000000000000000 : ℝ)) (X := (50036429810872959509/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6053733991500609/100000000000000000000 : ℝ) ≤ ((26983405680471908493/26990000000000000000 : ℝ)+2*(88509203339/67475000000000 : ℝ)*(10389/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (26983405680471908493/26990000000000000000 : ℝ)+2*(88509203339/67475000000000 : ℝ)*(10389/100000 : ℝ)=(10000282273945839/10000000000000000 : ℝ) by norm_num, show 1+2*(6053733991500609/100000000000000000000 : ℝ)=(50006053733991500609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36429810872959509/100000000000000000000 : ℝ)+(6053733991500609/100000000000000000000 : ℝ) ≤ ((26983405680471908493/26990000000000000000 : ℝ)+(88509203339/67475000000000 : ℝ)*((15787/100000 : ℝ)+(10389/100000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (26983405680471908493/26990000000000000000 : ℝ)+(88509203339/67475000000000 : ℝ)*((15787/100000 : ℝ)+(10389/100000 : ℝ))=(10000990347572551/10000000000000000 : ℝ) by norm_num, show 1+(36429810872959509/100000000000000000000 : ℝ)+(6053733991500609/100000000000000000000 : ℝ)=(50021241772432230059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36429810872959509/100000000000000000000 : ℝ) ≤ ((26983405680471908493/26990000000000000000 : ℝ)+2*(88509203339/67475000000000 : ℝ)*(15787/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (26983405680471908493/26990000000000000000 : ℝ)+2*(88509203339/67475000000000 : ℝ)*(15787/100000 : ℝ)=(10001698421199263/10000000000000000 : ℝ) by norm_num, show 1+2*(36429810872959509/100000000000000000000 : ℝ)=(50036429810872959509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26983405680471908493/26990000000000000000 : ℝ)*(X 1 0+X 2 0)+(88509203339/67475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (15787/100000 : ℝ)) (c := (26983405680471908493/26990000000000000000 : ℝ)) (alpha := (88509203339/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26983405680471908493/26990000000000000000 : ℝ)*(X 0 1+X 2 1)+(88509203339/67475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (15787/100000 : ℝ)) (c := (26983405680471908493/26990000000000000000 : ℝ)) (alpha := (88509203339/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26983405680471908493/26990000000000000000 : ℝ)*(X 0 2+X 1 2)+(88509203339/67475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (15787/100000 : ℝ)) (c := (26983405680471908493/26990000000000000000 : ℝ)) (alpha := (88509203339/67475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-983428793/5000000000 : ℝ)*X 0 0+(5416875403/10000000000 : ℝ)*X 0 1+(5238812471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334345763/625000000 : ℝ)*X 1 0+(-1028840201/5000000000 : ℝ)*X 1 1+(523881239/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349532229/10000000000 : ℝ)*X 2 0+(1309703071/2500000000 : ℝ)*X 2 1+(-411536103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075685801/2500000000 : ℝ)*X 0 0+(10284343/25000000 : ℝ)*X 0 1+(1124877731/2500000000 : ℝ)*X 0 2+(1075685801/2500000000 : ℝ)*X 1 0+(10284343/25000000 : ℝ)*X 1 1+(1124877731/2500000000 : ℝ)*X 1 2+(1075685801/2500000000 : ℝ)*X 2 0+(10284343/25000000 : ℝ)*X 2 1+(1124877731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966872479/10000000000 : ℝ)*X 0 0+(261976127/500000000 : ℝ)*X 0 1+(21156881/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325805829/2500000000 : ℝ)*X 1 0+(-940165677/5000000000 : ℝ)*X 1 1+(1354040373/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303223001/10000000000 : ℝ)*X 2 0+(169255057/312500000 : ℝ)*X 2 1+(-1880331329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151387971/5000000000 : ℝ)*X 0 0+(899594659/2000000000 : ℝ)*X 0 1+(4115283939/10000000000 : ℝ)*X 0 2+(2151387971/5000000000 : ℝ)*X 1 0+(899594659/2000000000 : ℝ)*X 1 1+(4115283939/10000000000 : ℝ)*X 1 2+(2151387971/5000000000 : ℝ)*X 2 0+(899594659/2000000000 : ℝ)*X 2 1+(4115283939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30972106143177803010357/2699000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1965451501/100000000000000 : ℝ)*(base19) + (975981729/50000000000000 : ℝ)*(base23) + (343611843/100000000000000 : ℝ)*(upper3) + (19009191/100000000000000 : ℝ)*(upper4) + (190205631/100000000000000 : ℝ)*(upper5) + (410413939468307/10000000000000 : ℝ)*(major0) + (410413939468307/10000000000000 : ℝ)*(major1) + (410413939468307/10000000000000 : ℝ)*(major2) + (5616027481323447/100000000000000 : ℝ)*(sp0) + (5616056341318917/100000000000000 : ℝ)*(sp1) + (70200704435087/1250000000000 : ℝ)*(sp2) + (2592205430372933/100000000000000 : ℝ)*(sp3) + (30825446971/100000000000000 : ℝ)*(sp4) + (14669709431/100000000000000 : ℝ)*(sp7) + (648055025020591/25000000000000 : ℝ)*(f.failure) + (5616058306770417/100000000000000 : ℝ)*(f.sum) + (7419199828767/2699000000000000000000000000 : ℝ)*base65 + (768828647109431351/269900000000000000000000000000000 : ℝ)*base67 + (1191700815193768649/269900000000000000000000000000000 : ℝ)*base70 + (1997735917586168649/269900000000000000000000000000000 : ℝ)*base72 + (2154858960999/539800000000000000000000000 : ℝ)*base73 + (3327837669479931351/269900000000000000000000000000000 : ℝ)*base75 + (351976162155768649/269900000000000000000000000000000 : ℝ)*base78 + (114052283795331351/269900000000000000000000000000000 : ℝ)*base79 + (209506220343/539800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (572797/2500000000000000000000 : ℝ)*base89 + (572797/2500000000000000000000 : ℝ)*base91 + (572797/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (930169913468268166957466733/337375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84143881/100000000000000 : ℝ)*(base8) + (58804007/20000000000000 : ℝ)*(base21) + (2454861/10000000000000 : ℝ)*(upper2) + (1712517/50000000000000 : ℝ)*(lower4) + (2068587875302227/50000000000000 : ℝ)*(major0) + (2068587875302227/50000000000000 : ℝ)*(major1) + (2068587875302227/50000000000000 : ℝ)*(major2) + (1165166241/100000000000000 : ℝ)*(sp1) + (3812914183/100000000000000 : ℝ)*(sp2) + (40161071/50000000000000 : ℝ)*(sp3) + (5661265095151789/100000000000000 : ℝ)*(sp4) + (5661264014129429/100000000000000 : ℝ)*(sp5) + (1415315268090363/25000000000000 : ℝ)*(sp6) + (2613086149688419/100000000000000 : ℝ)*(sp7) + (2613086230010561/100000000000000 : ℝ)*(f.failure) + (566126517929567/10000000000000 : ℝ)*(f.sum) + (145174896516201/13495000000000000000000000000 : ℝ)*base66 + (3046977121026813911/1349500000000000000000000000000000 : ℝ)*base67 + (5154464041529186089/1349500000000000000000000000000000 : ℝ)*base70 + (8514349015376686089/1349500000000000000000000000000000 : ℝ)*base72 + (18896831045591/13495000000000000000000000000 : ℝ)*base74 + (1579484906352186089/1349500000000000000000000000000000 : ℝ)*base76 + (9571688563493186089/1349500000000000000000000000000000 : ℝ)*base78 + (16389882660793186089/1349500000000000000000000000000000 : ℝ)*base80 + (3674459633737/1686875000000000000000000000 : ℝ)*base82 + (83144787/10000000000000000000000 : ℝ)*base89 + (83144787/10000000000000000000000 : ℝ)*base91 + (83144787/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1433_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (467/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_s4_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967740281/10000000000 : ℝ)*x 0 + (5409346869/10000000000 : ℝ)*x 1 + (5245759447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967740281/10000000000 : ℝ)^4393 ≤ (6002620237679/50000000000000 : ℝ)^3369 := by
    have hnat : (1967740281 : ℕ)^4393*50000000000000^3369 ≤ 6002620237679^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967740281 10000000000 6002620237679 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409346869/10000000000 : ℝ)^4393 ≤ (44878134979949/100000000000000 : ℝ)^3369 := by
    have hnat : (5409346869 : ℕ)^4393*100000000000000^3369 ≤ 44878134979949^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409346869 10000000000 44878134979949 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245759447/10000000000 : ℝ)^4393 ≤ (21558312260803/50000000000000 : ℝ)^3369 := by
    have hnat : (5245759447 : ℕ)^4393*50000000000000^3369 ≤ 21558312260803^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245759447 10000000000 21558312260803 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967740281/10000000000 : ℝ), (5409346869/10000000000 : ℝ), (5245759447/10000000000 : ℝ)] ![(6002620237679/50000000000000 : ℝ), (44878134979949/100000000000000 : ℝ), (21558312260803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967740281/10000000000 : ℝ)|^4393 ≤ (6002620237679/50000000000000 : ℝ)^3369
        have hw : |(-1967740281/10000000000 : ℝ)|=(1967740281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409346869/10000000000 : ℝ)|^4393 ≤ (44878134979949/100000000000000 : ℝ)^3369
        have hw : |(5409346869/10000000000 : ℝ)|=(5409346869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245759447/10000000000 : ℝ)|^4393 ≤ (21558312260803/50000000000000 : ℝ)^3369
        have hw : |(5245759447/10000000000 : ℝ)|=(5245759447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069517449/2000000000 : ℝ)*x 0 + (-512761513/2500000000 : ℝ)*x 1 + (2622879849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069517449/2000000000 : ℝ)^4393 ≤ (44211176821429/100000000000000 : ℝ)^3369 := by
    have hnat : (1069517449 : ℕ)^4393*100000000000000^3369 ≤ 44211176821429^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069517449 2000000000 44211176821429 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512761513/2500000000 : ℝ)^4393 ≤ (12672195953739/100000000000000 : ℝ)^3369 := by
    have hnat : (512761513 : ℕ)^4393*100000000000000^3369 ≤ 12672195953739^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512761513 2500000000 12672195953739 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622879849/5000000000 : ℝ)^4393 ≤ (21558313605859/50000000000000 : ℝ)^3369 := by
    have hnat : (2622879849 : ℕ)^4393*50000000000000^3369 ≤ 21558313605859^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622879849 5000000000 21558313605859 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069517449/2000000000 : ℝ), (-512761513/2500000000 : ℝ), (2622879849/5000000000 : ℝ)] ![(44211176821429/100000000000000 : ℝ), (12672195953739/100000000000000 : ℝ), (21558313605859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069517449/2000000000 : ℝ)|^4393 ≤ (44211176821429/100000000000000 : ℝ)^3369
        have hw : |(1069517449/2000000000 : ℝ)|=(1069517449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512761513/2500000000 : ℝ)|^4393 ≤ (12672195953739/100000000000000 : ℝ)^3369
        have hw : |(-512761513/2500000000 : ℝ)|=(512761513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622879849/5000000000 : ℝ)|^4393 ≤ (21558313605859/50000000000000 : ℝ)^3369
        have hw : |(2622879849/5000000000 : ℝ)|=(2622879849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347587259/10000000000 : ℝ)*x 0 + (131143993/250000000 : ℝ)*x 1 + (-512761501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347587259/10000000000 : ℝ)^4393 ≤ (8842235394471/20000000000000 : ℝ)^3369 := by
    have hnat : (5347587259 : ℕ)^4393*20000000000000^3369 ≤ 8842235394471^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347587259 10000000000 8842235394471 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131143993/250000000 : ℝ)^4393 ≤ (8623325489501/20000000000000 : ℝ)^3369 := by
    have hnat : (131143993 : ℕ)^4393*20000000000000^3369 ≤ 8623325489501^3369*250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131143993 250000000 8623325489501 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512761501/2500000000 : ℝ)^4393 ≤ (3168048891759/25000000000000 : ℝ)^3369 := by
    have hnat : (512761501 : ℕ)^4393*25000000000000^3369 ≤ 3168048891759^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512761501 2500000000 3168048891759 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347587259/10000000000 : ℝ), (131143993/250000000 : ℝ), (-512761501/2500000000 : ℝ)] ![(8842235394471/20000000000000 : ℝ), (8623325489501/20000000000000 : ℝ), (3168048891759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347587259/10000000000 : ℝ)|^4393 ≤ (8842235394471/20000000000000 : ℝ)^3369
        have hw : |(5347587259/10000000000 : ℝ)|=(5347587259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131143993/250000000 : ℝ)|^4393 ≤ (8623325489501/20000000000000 : ℝ)^3369
        have hw : |(131143993/250000000 : ℝ)|=(131143993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512761501/2500000000 : ℝ)|^4393 ≤ (3168048891759/25000000000000 : ℝ)^3369
        have hw : |(-512761501/2500000000 : ℝ)|=(512761501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430328293/1000000000 : ℝ)*x 0 + (4129352799/10000000000 : ℝ)*x 1 + (2241882719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430328293/1000000000 : ℝ)^4393 ≤ (133215326219/400000000000 : ℝ)^3369 := by
    have hnat : (430328293 : ℕ)^4393*400000000000^3369 ≤ 133215326219^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430328293 1000000000 133215326219 400000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129352799/10000000000 : ℝ)^4393 ≤ (31559504842553/100000000000000 : ℝ)^3369 := by
    have hnat : (4129352799 : ℕ)^4393*100000000000000^3369 ≤ 31559504842553^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129352799 10000000000 31559504842553 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241882719/5000000000 : ℝ)^4393 ≤ (35136663589041/100000000000000 : ℝ)^3369 := by
    have hnat : (2241882719 : ℕ)^4393*100000000000000^3369 ≤ 35136663589041^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241882719 5000000000 35136663589041 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430328293/1000000000 : ℝ), (4129352799/10000000000 : ℝ), (2241882719/5000000000 : ℝ)] ![(133215326219/400000000000 : ℝ), (31559504842553/100000000000000 : ℝ), (35136663589041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430328293/1000000000 : ℝ)|^4393 ≤ (133215326219/400000000000 : ℝ)^3369
        have hw : |(430328293/1000000000 : ℝ)|=(430328293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129352799/10000000000 : ℝ)|^4393 ≤ (31559504842553/100000000000000 : ℝ)^3369
        have hw : |(4129352799/10000000000 : ℝ)|=(4129352799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241882719/5000000000 : ℝ)|^4393 ≤ (35136663589041/100000000000000 : ℝ)^3369
        have hw : |(2241882719/5000000000 : ℝ)|=(2241882719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-491938029/2500000000 : ℝ)*x 0 + (5246359137/10000000000 : ℝ)*x 1 + (5408744027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491938029/2500000000 : ℝ)^4393 ≤ (3001333656969/25000000000000 : ℝ)^3369 := by
    have hnat : (491938029 : ℕ)^4393*25000000000000^3369 ≤ 3001333656969^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491938029 2500000000 3001333656969 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246359137/10000000000 : ℝ)^4393 ≤ (2156152592823/5000000000000 : ℝ)^3369 := by
    have hnat : (5246359137 : ℕ)^4393*5000000000000^3369 ≤ 2156152592823^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246359137 10000000000 2156152592823 5000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408744027/10000000000 : ℝ)^4393 ≤ (11217903374457/25000000000000 : ℝ)^3369 := by
    have hnat : (5408744027 : ℕ)^4393*25000000000000^3369 ≤ 11217903374457^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408744027 10000000000 11217903374457 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491938029/2500000000 : ℝ), (5246359137/10000000000 : ℝ), (5408744027/10000000000 : ℝ)] ![(3001333656969/25000000000000 : ℝ), (2156152592823/5000000000000 : ℝ), (11217903374457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491938029/2500000000 : ℝ)|^4393 ≤ (3001333656969/25000000000000 : ℝ)^3369
        have hw : |(-491938029/2500000000 : ℝ)|=(491938029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246359137/10000000000 : ℝ)|^4393 ≤ (2156152592823/5000000000000 : ℝ)^3369
        have hw : |(5246359137/10000000000 : ℝ)|=(5246359137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408744027/10000000000 : ℝ)|^4393 ≤ (11217903374457/25000000000000 : ℝ)^3369
        have hw : |(5408744027/10000000000 : ℝ)|=(5408744027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652521377/5000000000 : ℝ)*x 0 + (-377612303/2000000000 : ℝ)*x 1 + (2704372013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652521377/5000000000 : ℝ)^4393 ≤ (21876543135353/50000000000000 : ℝ)^3369 := by
    have hnat : (2652521377 : ℕ)^4393*50000000000000^3369 ≤ 21876543135353^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652521377 5000000000 21876543135353 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377612303/2000000000 : ℝ)^4393 ≤ (11375300237333/100000000000000 : ℝ)^3369 := by
    have hnat : (377612303 : ℕ)^4393*100000000000000^3369 ≤ 11375300237333^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377612303 2000000000 11375300237333 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704372013/5000000000 : ℝ)^4393 ≤ (4487161348701/10000000000000 : ℝ)^3369 := by
    have hnat : (2704372013 : ℕ)^4393*10000000000000^3369 ≤ 4487161348701^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704372013 5000000000 4487161348701 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652521377/5000000000 : ℝ), (-377612303/2000000000 : ℝ), (2704372013/5000000000 : ℝ)] ![(21876543135353/50000000000000 : ℝ), (11375300237333/100000000000000 : ℝ), (4487161348701/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652521377/5000000000 : ℝ)|^4393 ≤ (21876543135353/50000000000000 : ℝ)^3369
        have hw : |(2652521377/5000000000 : ℝ)|=(2652521377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377612303/2000000000 : ℝ)|^4393 ≤ (11375300237333/100000000000000 : ℝ)^3369
        have hw : |(-377612303/2000000000 : ℝ)|=(377612303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704372013/5000000000 : ℝ)|^4393 ≤ (4487161348701/10000000000000 : ℝ)^3369
        have hw : |(2704372013/5000000000 : ℝ)|=(2704372013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212201709/400000000 : ℝ)*x 0 + (1352186009/2500000000 : ℝ)*x 1 + (-1888061539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212201709/400000000 : ℝ)^4393 ≤ (43753085958833/100000000000000 : ℝ)^3369 := by
    have hnat : (212201709 : ℕ)^4393*100000000000000^3369 ≤ 43753085958833^3369*400000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212201709 400000000 43753085958833 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352186009/2500000000 : ℝ)^4393 ≤ (44871613595187/100000000000000 : ℝ)^3369 := by
    have hnat : (1352186009 : ℕ)^4393*100000000000000^3369 ≤ 44871613595187^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352186009 2500000000 44871613595187 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888061539/10000000000 : ℝ)^4393 ≤ (284382510647/2500000000000 : ℝ)^3369 := by
    have hnat : (1888061539 : ℕ)^4393*2500000000000^3369 ≤ 284382510647^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888061539 10000000000 284382510647 2500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212201709/400000000 : ℝ), (1352186009/2500000000 : ℝ), (-1888061539/10000000000 : ℝ)] ![(43753085958833/100000000000000 : ℝ), (44871613595187/100000000000000 : ℝ), (284382510647/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212201709/400000000 : ℝ)|^4393 ≤ (43753085958833/100000000000000 : ℝ)^3369
        have hw : |(212201709/400000000 : ℝ)|=(212201709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352186009/2500000000 : ℝ)|^4393 ≤ (44871613595187/100000000000000 : ℝ)^3369
        have hw : |(1352186009/2500000000 : ℝ)|=(1352186009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888061539/10000000000 : ℝ)|^4393 ≤ (284382510647/2500000000000 : ℝ)^3369
        have hw : |(-1888061539/10000000000 : ℝ)|=(1888061539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s4_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151654333/5000000000 : ℝ)*x 0 + (4482466401/10000000000 : ℝ)*x 1 + (258166161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151654333/5000000000 : ℝ)^4393 ≤ (33304091269093/100000000000000 : ℝ)^3369 := by
    have hnat : (2151654333 : ℕ)^4393*100000000000000^3369 ≤ 33304091269093^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151654333 5000000000 33304091269093 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482466401/10000000000 : ℝ)^4393 ≤ (8780847562213/25000000000000 : ℝ)^3369 := by
    have hnat : (4482466401 : ℕ)^4393*25000000000000^3369 ≤ 8780847562213^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482466401 10000000000 8780847562213 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258166161/625000000 : ℝ)^4393 ≤ (31572518466931/100000000000000 : ℝ)^3369 := by
    have hnat : (258166161 : ℕ)^4393*100000000000000^3369 ≤ 31572518466931^3369*625000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258166161 625000000 31572518466931 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151654333/5000000000 : ℝ), (4482466401/10000000000 : ℝ), (258166161/625000000 : ℝ)] ![(33304091269093/100000000000000 : ℝ), (8780847562213/25000000000000 : ℝ), (31572518466931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151654333/5000000000 : ℝ)|^4393 ≤ (33304091269093/100000000000000 : ℝ)^3369
        have hw : |(2151654333/5000000000 : ℝ)|=(2151654333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482466401/10000000000 : ℝ)|^4393 ≤ (8780847562213/25000000000000 : ℝ)^3369
        have hw : |(4482466401/10000000000 : ℝ)|=(4482466401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258166161/625000000 : ℝ)|^4393 ≤ (31572518466931/100000000000000 : ℝ)^3369
        have hw : |(258166161/625000000 : ℝ)|=(258166161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14787/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (467/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (467/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (467/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (467/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (549/128 : ℝ) ≤ (8270671613260117/100000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^549 ≤ (8270671613260117/100000000000000000000 : ℝ)^128 := by
      have hnat : (11173 : ℕ)^549*100000000000000000000^128 ≤ 8270671613260117^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 8270671613260117 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (8270671613260117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (467/3125 : ℝ) ^ (549/128 : ℝ) ≤ (14394837489568599/50000000000000000000 : ℝ) := by
    have hpowers : (467/3125 : ℝ)^549 ≤ (14394837489568599/50000000000000000000 : ℝ)^128 := by
      have hnat : (467 : ℕ)^549*50000000000000000000^128 ≤ 14394837489568599^128*3125^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 3125 14394837489568599 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/3125 : ℝ)) (X := (14394837489568599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008270671613260117/50000000000000000000 : ℝ) ≤ (10000385638918017/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50008270671613260117/50000000000000000000 : ℝ)^128 ≤ (10000385638918017/10000000000000000 : ℝ)^549 := by
      have hnat : (50008270671613260117 : ℕ)^128*10000000000000000^549 ≤ 10000385638918017^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008270671613260117 50000000000000000000 10000385638918017 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000385638918017/10000000000000000 : ℝ)) (X := (50008270671613260117/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007412069318479463/20000000000000000000 : ℝ) ≤ (10000863943612971/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (20007412069318479463/20000000000000000000 : ℝ)^128 ≤ (10000863943612971/10000000000000000 : ℝ)^549 := by
      have hnat : (20007412069318479463 : ℕ)^128*10000000000000000^549 ≤ 10000863943612971^549*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007412069318479463 20000000000000000000 10000863943612971 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000863943612971/10000000000000000 : ℝ)) (X := (20007412069318479463/20000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014394837489568599/25000000000000000000 : ℝ) ≤ (400053689932317/400000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25014394837489568599/25000000000000000000 : ℝ)^128 ≤ (400053689932317/400000000000000 : ℝ)^549 := by
      have hnat : (25014394837489568599 : ℕ)^128*400000000000000^549 ≤ 400053689932317^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014394837489568599 25000000000000000000 400053689932317 400000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400053689932317/400000000000000 : ℝ)) (X := (25014394837489568599/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8270671613260117/100000000000000000000 : ℝ) ≤ ((4188974005294044447/4190000000000000000 : ℝ)+2*(26572483053/20950000000000 : ℝ)*(11173/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (4188974005294044447/4190000000000000000 : ℝ)+2*(26572483053/20950000000000 : ℝ)*(11173/100000 : ℝ)=(10000385638918017/10000000000000000 : ℝ) by norm_num, show 1+2*(8270671613260117/100000000000000000000 : ℝ)=(50008270671613260117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14394837489568599/50000000000000000000 : ℝ)+(8270671613260117/100000000000000000000 : ℝ) ≤ ((4188974005294044447/4190000000000000000 : ℝ)+(26572483053/20950000000000 : ℝ)*((467/3125 : ℝ)+(11173/100000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (4188974005294044447/4190000000000000000 : ℝ)+(26572483053/20950000000000 : ℝ)*((467/3125 : ℝ)+(11173/100000 : ℝ))=(10000863943612971/10000000000000000 : ℝ) by norm_num, show 1+(14394837489568599/50000000000000000000 : ℝ)+(8270671613260117/100000000000000000000 : ℝ)=(20007412069318479463/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14394837489568599/50000000000000000000 : ℝ) ≤ ((4188974005294044447/4190000000000000000 : ℝ)+2*(26572483053/20950000000000 : ℝ)*(467/3125 : ℝ))^(549/128 : ℝ) := by
    rw [show (4188974005294044447/4190000000000000000 : ℝ)+2*(26572483053/20950000000000 : ℝ)*(467/3125 : ℝ)=(400053689932317/400000000000000 : ℝ) by norm_num, show 1+2*(14394837489568599/50000000000000000000 : ℝ)=(25014394837489568599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4188974005294044447/4190000000000000000 : ℝ)*(X 1 0+X 2 0)+(26572483053/20950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (4188974005294044447/4190000000000000000 : ℝ)) (alpha := (26572483053/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4188974005294044447/4190000000000000000 : ℝ)*(X 0 1+X 2 1)+(26572483053/20950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (4188974005294044447/4190000000000000000 : ℝ)) (alpha := (26572483053/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4188974005294044447/4190000000000000000 : ℝ)*(X 0 2+X 1 2)+(26572483053/20950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (467/3125 : ℝ)) (c := (4188974005294044447/4190000000000000000 : ℝ)) (alpha := (26572483053/20950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1967740281/10000000000 : ℝ)*X 0 0+(5409346869/10000000000 : ℝ)*X 0 1+(5245759447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069517449/2000000000 : ℝ)*X 1 0+(-512761513/2500000000 : ℝ)*X 1 1+(2622879849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347587259/10000000000 : ℝ)*X 2 0+(131143993/250000000 : ℝ)*X 2 1+(-512761501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430328293/1000000000 : ℝ)*X 0 0+(4129352799/10000000000 : ℝ)*X 0 1+(2241882719/5000000000 : ℝ)*X 0 2+(430328293/1000000000 : ℝ)*X 1 0+(4129352799/10000000000 : ℝ)*X 1 1+(2241882719/5000000000 : ℝ)*X 1 2+(430328293/1000000000 : ℝ)*X 2 0+(4129352799/10000000000 : ℝ)*X 2 1+(2241882719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-491938029/2500000000 : ℝ)*X 0 0+(5246359137/10000000000 : ℝ)*X 0 1+(5408744027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652521377/5000000000 : ℝ)*X 1 0+(-377612303/2000000000 : ℝ)*X 1 1+(2704372013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212201709/400000000 : ℝ)*X 2 0+(1352186009/2500000000 : ℝ)*X 2 1+(-1888061539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151654333/5000000000 : ℝ)*X 0 0+(4482466401/10000000000 : ℝ)*X 0 1+(258166161/625000000 : ℝ)*X 0 2+(2151654333/5000000000 : ℝ)*X 1 0+(4482466401/10000000000 : ℝ)*X 1 1+(258166161/625000000 : ℝ)*X 1 2+(2151654333/5000000000 : ℝ)*X 2 0+(4482466401/10000000000 : ℝ)*X 2 1+(258166161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3022570913851028749791/523750000000000000000000000 : ℝ) := by norm_num
    linear_combination (284855241/50000000000000 : ℝ)*(base19) + (113449771/20000000000000 : ℝ)*(base23) + (9874547/100000000000000 : ℝ)*(lower2) + (38569981/50000000000000 : ℝ)*(upper3) + (12677659/10000000000000 : ℝ)*(upper5) + (4467282568062987/100000000000000 : ℝ)*(major0) + (4467282568062987/100000000000000 : ℝ)*(major1) + (4467282568062987/100000000000000 : ℝ)*(major2) + (1222591655172313/20000000000000 : ℝ)*(sp0) + (1528244751426143/25000000000000 : ℝ)*(sp1) + (6112979008166199/100000000000000 : ℝ)*(sp2) + (282157785147527/10000000000000 : ℝ)*(sp3) + (1331222093/6250000000000 : ℝ)*(sp4) + (187921709/2500000000000 : ℝ)*(sp7) + (2821585368343631/100000000000000 : ℝ)*(f.failure) + (3056489787707527/50000000000000 : ℝ)*(f.sum) + (3834845861643/2095000000000000000000000000 : ℝ)*base66 + (3593763399646783189/419000000000000000000000000000000 : ℝ)*base67 + (5418306684666783189/419000000000000000000000000000000 : ℝ)*base69 + (1098814559264216811/419000000000000000000000000000000 : ℝ)*base72 + (174760944297/130937500000000000000000000 : ℝ)*base73 + (130078127308216811/419000000000000000000000000000000 : ℝ)*base76 + (1627372333283216811/419000000000000000000000000000000 : ℝ)*base78 + (4817036229705783189/419000000000000000000000000000000 : ℝ)*base79 + (7690261381171/1047500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (25824477/10000000000000000000000 : ℝ)*base89 + (25824477/10000000000000000000000 : ℝ)*base91 + (25824477/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (744931231337685352288852191/104750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306603897/25000000000000 : ℝ)*(base19) + (322519153/25000000000000 : ℝ)*(base23) + (153351119/100000000000000 : ℝ)*(upper3) + (45585957/100000000000000 : ℝ)*(lower4) + (32816807/25000000000000 : ℝ)*(upper5) + (2250166847893383/50000000000000 : ℝ)*(major0) + (2250166847893383/50000000000000 : ℝ)*(major1) + (2250166847893383/50000000000000 : ℝ)*(major2) + (2510129987/10000000000000 : ℝ)*(sp1) + (5304441047/20000000000000 : ℝ)*(sp2) + (6158206326216451/100000000000000 : ℝ)*(sp4) + (3079089999250497/50000000000000 : ℝ)*(sp5) + (1539544628483651/25000000000000 : ℝ)*(sp6) + (568492165661311/20000000000000 : ℝ)*(sp7) + (568492165661311/20000000000000 : ℝ)*(f.failure) + (6158206326216451/100000000000000 : ℝ)*(f.sum) + (3661116210183/1047500000000000000000000000 : ℝ)*base65 + (3108612404429994201/209500000000000000000000000000000 : ℝ)*base67 + (2808915842537494201/209500000000000000000000000000000 : ℝ)*base69 + (2600734142446994201/209500000000000000000000000000000 : ℝ)*base71 + (4983261099721/2095000000000000000000000000 : ℝ)*base73 + (115623034330994201/209500000000000000000000000000000 : ℝ)*base75 + (2489405603826494201/209500000000000000000000000000000 : ℝ)*base77 + (3261213638038494201/209500000000000000000000000000000 : ℝ)*base79 + (1530609690679/523750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (24354963/2000000000000000000000 : ℝ)*base90 + (24354963/2000000000000000000000 : ℝ)*base92 + (24354963/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (467/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_s5_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-983934443/5000000000 : ℝ)*x 0 + (108163733/200000000 : ℝ)*x 1 + (5246835013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983934443/5000000000 : ℝ)^4393 ≤ (12006263592703/100000000000000 : ℝ)^3369 := by
    have hnat : (983934443 : ℕ)^4393*100000000000000^3369 ≤ 12006263592703^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983934443 5000000000 12006263592703 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108163733/200000000 : ℝ)^4393 ≤ (22432792023957/50000000000000 : ℝ)^3369 := by
    have hnat : (108163733 : ℕ)^4393*50000000000000^3369 ≤ 22432792023957^3369*200000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108163733 200000000 22432792023957 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246835013/10000000000 : ℝ)^4393 ≤ (43128152341209/100000000000000 : ℝ)^3369 := by
    have hnat : (5246835013 : ℕ)^4393*100000000000000^3369 ≤ 43128152341209^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246835013 10000000000 43128152341209 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983934443/5000000000 : ℝ), (108163733/200000000 : ℝ), (5246835013/10000000000 : ℝ)] ![(12006263592703/100000000000000 : ℝ), (22432792023957/50000000000000 : ℝ), (43128152341209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983934443/5000000000 : ℝ)|^4393 ≤ (12006263592703/100000000000000 : ℝ)^3369
        have hw : |(-983934443/5000000000 : ℝ)|=(983934443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108163733/200000000 : ℝ)|^4393 ≤ (22432792023957/50000000000000 : ℝ)^3369
        have hw : |(108163733/200000000 : ℝ)|=(108163733/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246835013/10000000000 : ℝ)|^4393 ≤ (43128152341209/100000000000000 : ℝ)^3369
        have hw : |(5246835013/10000000000 : ℝ)|=(5246835013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347288001/10000000000 : ℝ)*x 0 + (-1025007913/5000000000 : ℝ)*x 1 + (2623417507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347288001/10000000000 : ℝ)^4393 ≤ (44207950882461/100000000000000 : ℝ)^3369 := by
    have hnat : (5347288001 : ℕ)^4393*100000000000000^3369 ≤ 44207950882461^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347288001 10000000000 44207950882461 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025007913/5000000000 : ℝ)^4393 ≤ (12663896757967/100000000000000 : ℝ)^3369 := by
    have hnat : (1025007913 : ℕ)^4393*100000000000000^3369 ≤ 12663896757967^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025007913 5000000000 12663896757967 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623417507/5000000000 : ℝ)^4393 ≤ (43128152351927/100000000000000 : ℝ)^3369 := by
    have hnat : (2623417507 : ℕ)^4393*100000000000000^3369 ≤ 43128152351927^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623417507 5000000000 43128152351927 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347288001/10000000000 : ℝ), (-1025007913/5000000000 : ℝ), (2623417507/5000000000 : ℝ)] ![(44207950882461/100000000000000 : ℝ), (12663896757967/100000000000000 : ℝ), (43128152351927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347288001/10000000000 : ℝ)|^4393 ≤ (44207950882461/100000000000000 : ℝ)^3369
        have hw : |(5347288001/10000000000 : ℝ)|=(5347288001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025007913/5000000000 : ℝ)|^4393 ≤ (12663896757967/100000000000000 : ℝ)^3369
        have hw : |(-1025007913/5000000000 : ℝ)|=(1025007913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623417507/5000000000 : ℝ)|^4393 ≤ (43128152351927/100000000000000 : ℝ)^3369
        have hw : |(2623417507/5000000000 : ℝ)|=(2623417507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347288001/10000000000 : ℝ)*x 0 + (2623417507/5000000000 : ℝ)*x 1 + (-1025007913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347288001/10000000000 : ℝ)^4393 ≤ (44207950882461/100000000000000 : ℝ)^3369 := by
    have hnat : (5347288001 : ℕ)^4393*100000000000000^3369 ≤ 44207950882461^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347288001 10000000000 44207950882461 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623417507/5000000000 : ℝ)^4393 ≤ (43128152351927/100000000000000 : ℝ)^3369 := by
    have hnat : (2623417507 : ℕ)^4393*100000000000000^3369 ≤ 43128152351927^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623417507 5000000000 43128152351927 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025007913/5000000000 : ℝ)^4393 ≤ (12663896757967/100000000000000 : ℝ)^3369 := by
    have hnat : (1025007913 : ℕ)^4393*100000000000000^3369 ≤ 12663896757967^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025007913 5000000000 12663896757967 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347288001/10000000000 : ℝ), (2623417507/5000000000 : ℝ), (-1025007913/5000000000 : ℝ)] ![(44207950882461/100000000000000 : ℝ), (43128152351927/100000000000000 : ℝ), (12663896757967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347288001/10000000000 : ℝ)|^4393 ≤ (44207950882461/100000000000000 : ℝ)^3369
        have hw : |(5347288001/10000000000 : ℝ)|=(5347288001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623417507/5000000000 : ℝ)|^4393 ≤ (43128152351927/100000000000000 : ℝ)^3369
        have hw : |(2623417507/5000000000 : ℝ)|=(2623417507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025007913/5000000000 : ℝ)|^4393 ≤ (12663896757967/100000000000000 : ℝ)^3369
        have hw : |(-1025007913/5000000000 : ℝ)|=(1025007913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151681163/5000000000 : ℝ)*x 0 + (64558827/156250000 : ℝ)*x 1 + (448133411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151681163/5000000000 : ℝ)^4393 ≤ (16652316389729/50000000000000 : ℝ)^3369 := by
    have hnat : (2151681163 : ℕ)^4393*50000000000000^3369 ≤ 16652316389729^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151681163 5000000000 16652316389729 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64558827/156250000 : ℝ)^4393 ≤ (31583545562041/100000000000000 : ℝ)^3369 := by
    have hnat : (64558827 : ℕ)^4393*100000000000000^3369 ≤ 31583545562041^3369*156250000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64558827 156250000 31583545562041 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448133411/1000000000 : ℝ)^4393 ≤ (35111821644717/100000000000000 : ℝ)^3369 := by
    have hnat : (448133411 : ℕ)^4393*100000000000000^3369 ≤ 35111821644717^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448133411 1000000000 35111821644717 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151681163/5000000000 : ℝ), (64558827/156250000 : ℝ), (448133411/1000000000 : ℝ)] ![(16652316389729/50000000000000 : ℝ), (31583545562041/100000000000000 : ℝ), (35111821644717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151681163/5000000000 : ℝ)|^4393 ≤ (16652316389729/50000000000000 : ℝ)^3369
        have hw : |(2151681163/5000000000 : ℝ)|=(2151681163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64558827/156250000 : ℝ)|^4393 ≤ (31583545562041/100000000000000 : ℝ)^3369
        have hw : |(64558827/156250000 : ℝ)|=(64558827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448133411/1000000000 : ℝ)|^4393 ≤ (35111821644717/100000000000000 : ℝ)^3369
        have hw : |(448133411/1000000000 : ℝ)|=(448133411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967881123/10000000000 : ℝ)*x 0 + (5247417283/10000000000 : ℝ)*x 1 + (5407600697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967881123/10000000000 : ℝ)^4393 ≤ (300159023631/2500000000000 : ℝ)^3369 := by
    have hnat : (1967881123 : ℕ)^4393*2500000000000^3369 ≤ 300159023631^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967881123 10000000000 300159023631 2500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247417283/10000000000 : ℝ)^4393 ≤ (21567196679181/50000000000000 : ℝ)^3369 := by
    have hnat : (5247417283 : ℕ)^4393*50000000000000^3369 ≤ 21567196679181^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247417283 10000000000 21567196679181 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407600697/10000000000 : ℝ)^4393 ≤ (11214811419881/25000000000000 : ℝ)^3369 := by
    have hnat : (5407600697 : ℕ)^4393*25000000000000^3369 ≤ 11214811419881^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407600697 10000000000 11214811419881 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967881123/10000000000 : ℝ), (5247417283/10000000000 : ℝ), (5407600697/10000000000 : ℝ)] ![(300159023631/2500000000000 : ℝ), (21567196679181/50000000000000 : ℝ), (11214811419881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967881123/10000000000 : ℝ)|^4393 ≤ (300159023631/2500000000000 : ℝ)^3369
        have hw : |(-1967881123/10000000000 : ℝ)|=(1967881123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247417283/10000000000 : ℝ)|^4393 ≤ (21567196679181/50000000000000 : ℝ)^3369
        have hw : |(5247417283/10000000000 : ℝ)|=(5247417283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407600697/10000000000 : ℝ)|^4393 ≤ (11214811419881/25000000000000 : ℝ)^3369
        have hw : |(5407600697/10000000000 : ℝ)|=(5407600697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305323477/10000000000 : ℝ)*x 0 + (-1889251311/10000000000 : ℝ)*x 1 + (5407600767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305323477/10000000000 : ℝ)^4393 ≤ (21878052629697/50000000000000 : ℝ)^3369 := by
    have hnat : (5305323477 : ℕ)^4393*50000000000000^3369 ≤ 21878052629697^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305323477 10000000000 21878052629697 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889251311/10000000000 : ℝ)^4393 ≤ (1423081035869/12500000000000 : ℝ)^3369 := by
    have hnat : (1889251311 : ℕ)^4393*12500000000000^3369 ≤ 1423081035869^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889251311 10000000000 1423081035869 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407600767/10000000000 : ℝ)^4393 ≤ (8971849287343/20000000000000 : ℝ)^3369 := by
    have hnat : (5407600767 : ℕ)^4393*20000000000000^3369 ≤ 8971849287343^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407600767 10000000000 8971849287343 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305323477/10000000000 : ℝ), (-1889251311/10000000000 : ℝ), (5407600767/10000000000 : ℝ)] ![(21878052629697/50000000000000 : ℝ), (1423081035869/12500000000000 : ℝ), (8971849287343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305323477/10000000000 : ℝ)|^4393 ≤ (21878052629697/50000000000000 : ℝ)^3369
        have hw : |(5305323477/10000000000 : ℝ)|=(5305323477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889251311/10000000000 : ℝ)|^4393 ≤ (1423081035869/12500000000000 : ℝ)^3369
        have hw : |(-1889251311/10000000000 : ℝ)|=(1889251311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407600767/10000000000 : ℝ)|^4393 ≤ (8971849287343/20000000000000 : ℝ)^3369
        have hw : |(5407600767/10000000000 : ℝ)|=(5407600767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652662399/5000000000 : ℝ)*x 0 + (2703800037/5000000000 : ℝ)*x 1 + (-944625229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652662399/5000000000 : ℝ)^4393 ≤ (43756119465983/100000000000000 : ℝ)^3369 := by
    have hnat : (2652662399 : ℕ)^4393*100000000000000^3369 ≤ 43756119465983^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652662399 5000000000 43756119465983 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703800037/5000000000 : ℝ)^4393 ≤ (22429619470261/50000000000000 : ℝ)^3369 := by
    have hnat : (2703800037 : ℕ)^4393*50000000000000^3369 ≤ 22429619470261^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703800037 5000000000 22429619470261 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944625229/5000000000 : ℝ)^4393 ≤ (11384641584417/100000000000000 : ℝ)^3369 := by
    have hnat : (944625229 : ℕ)^4393*100000000000000^3369 ≤ 11384641584417^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944625229 5000000000 11384641584417 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652662399/5000000000 : ℝ), (2703800037/5000000000 : ℝ), (-944625229/5000000000 : ℝ)] ![(43756119465983/100000000000000 : ℝ), (22429619470261/50000000000000 : ℝ), (11384641584417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652662399/5000000000 : ℝ)|^4393 ≤ (43756119465983/100000000000000 : ℝ)^3369
        have hw : |(2652662399/5000000000 : ℝ)|=(2652662399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703800037/5000000000 : ℝ)|^4393 ≤ (22429619470261/50000000000000 : ℝ)^3369
        have hw : |(2703800037/5000000000 : ℝ)|=(2703800037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944625229/5000000000 : ℝ)|^4393 ≤ (11384641584417/100000000000000 : ℝ)^3369
        have hw : |(-944625229/5000000000 : ℝ)|=(944625229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s5_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (860677433/2000000000 : ℝ)*x 0 + (2240034987/5000000000 : ℝ)*x 1 + (826607079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860677433/2000000000 : ℝ)^4393 ≤ (33304883443141/100000000000000 : ℝ)^3369 := by
    have hnat : (860677433 : ℕ)^4393*100000000000000^3369 ≤ 33304883443141^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860677433 2000000000 33304883443141 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240034987/5000000000 : ℝ)^4393 ≤ (2193681689459/6250000000000 : ℝ)^3369 := by
    have hnat : (2240034987 : ℕ)^4393*6250000000000^3369 ≤ 2193681689459^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240034987 5000000000 2193681689459 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826607079/2000000000 : ℝ)^4393 ≤ (1974763094437/6250000000000 : ℝ)^3369 := by
    have hnat : (826607079 : ℕ)^4393*6250000000000^3369 ≤ 1974763094437^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826607079 2000000000 1974763094437 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860677433/2000000000 : ℝ), (2240034987/5000000000 : ℝ), (826607079/2000000000 : ℝ)] ![(33304883443141/100000000000000 : ℝ), (2193681689459/6250000000000 : ℝ), (1974763094437/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860677433/2000000000 : ℝ)|^4393 ≤ (33304883443141/100000000000000 : ℝ)^3369
        have hw : |(860677433/2000000000 : ℝ)|=(860677433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240034987/5000000000 : ℝ)|^4393 ≤ (2193681689459/6250000000000 : ℝ)^3369
        have hw : |(2240034987/5000000000 : ℝ)|=(2240034987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826607079/2000000000 : ℝ)|^4393 ≤ (1974763094437/6250000000000 : ℝ)^3369
        have hw : |(826607079/2000000000 : ℝ)|=(826607079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/50000 : ℝ) ^ (549/128 : ℝ) ≤ (4377108048217221/50000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^549 ≤ (4377108048217221/50000000000000000000 : ℝ)^128 := by
      have hnat : (5661 : ℕ)^549*50000000000000000000^128 ≤ 4377108048217221^128*50000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 4377108048217221 50000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (4377108048217221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14787/100000 : ℝ) ^ (549/128 : ℝ) ≤ (859832332036523/3125000000000000000 : ℝ) := by
    have hpowers : (14787/100000 : ℝ)^549 ≤ (859832332036523/3125000000000000000 : ℝ)^128 := by
      have hnat : (14787 : ℕ)^549*3125000000000000000^128 ≤ 859832332036523^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14787 100000 859832332036523 3125000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14787/100000 : ℝ)) (X := (859832332036523/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004377108048217221/25000000000000000000 : ℝ) ≤ (62502551148553/62500000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (25004377108048217221/25000000000000000000 : ℝ)^128 ≤ (62502551148553/62500000000000 : ℝ)^549 := by
      have hnat : (25004377108048217221 : ℕ)^128*62500000000000^549 ≤ 62502551148553^549*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004377108048217221 25000000000000000000 62502551148553 62500000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62502551148553/62500000000000 : ℝ)) (X := (25004377108048217221/25000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018134425360801589/50000000000000000000 : ℝ) ≤ (5000422747489933/5000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50018134425360801589/50000000000000000000 : ℝ)^128 ≤ (5000422747489933/5000000000000000 : ℝ)^549 := by
      have hnat : (50018134425360801589 : ℕ)^128*5000000000000000^549 ≤ 5000422747489933^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018134425360801589 50000000000000000000 5000422747489933 5000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000422747489933/5000000000000000 : ℝ)) (X := (50018134425360801589/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563359832332036523/1562500000000000000 : ℝ) ≤ (2500320701547813/2500000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (1563359832332036523/1562500000000000000 : ℝ)^128 ≤ (2500320701547813/2500000000000000 : ℝ)^549 := by
      have hnat : (1563359832332036523 : ℕ)^128*2500000000000000^549 ≤ 2500320701547813^549*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563359832332036523 1562500000000000000 2500320701547813 2500000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500320701547813/2500000000000000 : ℝ)) (X := (1563359832332036523/1562500000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4377108048217221/50000000000000000000 : ℝ) ≤ ((68733158495411029/68750000000000000 : ℝ)+2*(31236515099/24750000000000 : ℝ)*(5661/50000 : ℝ))^(549/128 : ℝ) := by
    rw [show (68733158495411029/68750000000000000 : ℝ)+2*(31236515099/24750000000000 : ℝ)*(5661/50000 : ℝ)=(62502551148553/62500000000000 : ℝ) by norm_num, show 1+2*(4377108048217221/50000000000000000000 : ℝ)=(25004377108048217221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(859832332036523/3125000000000000000 : ℝ)+(4377108048217221/50000000000000000000 : ℝ) ≤ ((68733158495411029/68750000000000000 : ℝ)+(31236515099/24750000000000 : ℝ)*((14787/100000 : ℝ)+(5661/50000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (68733158495411029/68750000000000000 : ℝ)+(31236515099/24750000000000 : ℝ)*((14787/100000 : ℝ)+(5661/50000 : ℝ))=(5000422747489933/5000000000000000 : ℝ) by norm_num, show 1+(859832332036523/3125000000000000000 : ℝ)+(4377108048217221/50000000000000000000 : ℝ)=(50018134425360801589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(859832332036523/3125000000000000000 : ℝ) ≤ ((68733158495411029/68750000000000000 : ℝ)+2*(31236515099/24750000000000 : ℝ)*(14787/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (68733158495411029/68750000000000000 : ℝ)+2*(31236515099/24750000000000 : ℝ)*(14787/100000 : ℝ)=(2500320701547813/2500000000000000 : ℝ) by norm_num, show 1+2*(859832332036523/3125000000000000000 : ℝ)=(1563359832332036523/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68733158495411029/68750000000000000 : ℝ)*(X 1 0+X 2 0)+(31236515099/24750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (68733158495411029/68750000000000000 : ℝ)) (alpha := (31236515099/24750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68733158495411029/68750000000000000 : ℝ)*(X 0 1+X 2 1)+(31236515099/24750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (68733158495411029/68750000000000000 : ℝ)) (alpha := (31236515099/24750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68733158495411029/68750000000000000 : ℝ)*(X 0 2+X 1 2)+(31236515099/24750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (68733158495411029/68750000000000000 : ℝ)) (alpha := (31236515099/24750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-983934443/5000000000 : ℝ)*X 0 0+(108163733/200000000 : ℝ)*X 0 1+(5246835013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347288001/10000000000 : ℝ)*X 1 0+(-1025007913/5000000000 : ℝ)*X 1 1+(2623417507/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347288001/10000000000 : ℝ)*X 2 0+(2623417507/5000000000 : ℝ)*X 2 1+(-1025007913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151681163/5000000000 : ℝ)*X 0 0+(64558827/156250000 : ℝ)*X 0 1+(448133411/1000000000 : ℝ)*X 0 2+(2151681163/5000000000 : ℝ)*X 1 0+(64558827/156250000 : ℝ)*X 1 1+(448133411/1000000000 : ℝ)*X 1 2+(2151681163/5000000000 : ℝ)*X 2 0+(64558827/156250000 : ℝ)*X 2 1+(448133411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1967881123/10000000000 : ℝ)*X 0 0+(5247417283/10000000000 : ℝ)*X 0 1+(5407600697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305323477/10000000000 : ℝ)*X 1 0+(-1889251311/10000000000 : ℝ)*X 1 1+(5407600767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652662399/5000000000 : ℝ)*X 2 0+(2703800037/5000000000 : ℝ)*X 2 1+(-944625229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860677433/2000000000 : ℝ)*X 0 0+(2240034987/5000000000 : ℝ)*X 0 1+(826607079/2000000000 : ℝ)*X 0 2+(860677433/2000000000 : ℝ)*X 1 0+(2240034987/5000000000 : ℝ)*X 1 1+(826607079/2000000000 : ℝ)*X 1 2+(860677433/2000000000 : ℝ)*X 2 0+(2240034987/5000000000 : ℝ)*X 2 1+(826607079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3573677357868144237803/825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (788133531/100000000000000 : ℝ)*(base19) + (734695453/100000000000000 : ℝ)*(base23) + (28574879/100000000000000 : ℝ)*(lower2) + (3384287/3125000000000 : ℝ)*(upper3) + (69430293/100000000000000 : ℝ)*(upper5) + (4529178911963839/100000000000000 : ℝ)*(major0) + (4529178911963839/100000000000000 : ℝ)*(major1) + (4529178911963839/100000000000000 : ℝ)*(major2) + (1549415321945917/25000000000000 : ℝ)*(sp0) + (387354818978573/6250000000000 : ℝ)*(sp1) + (3098838578547623/50000000000000 : ℝ)*(sp2) + (572134300226447/20000000000000 : ℝ)*(sp3) + (16604007031/100000000000000 : ℝ)*(sp4) + (4143306867/50000000000000 : ℝ)*(sp7) + (2860679787745969/100000000000000 : ℝ)*(f.failure) + (6197677891790699/100000000000000 : ℝ)*(f.sum) + (10270177689097/2475000000000000000000000000 : ℝ)*base65 + (16127166802672979/61875000000000000000000000000000 : ℝ)*base67 + (728742218883577021/61875000000000000000000000000000 : ℝ)*base70 + (219614370564547979/61875000000000000000000000000000 : ℝ)*base71 + (453424422911/1237500000000000000000000000 : ℝ)*base73 + (373209215157952021/61875000000000000000000000000000 : ℝ)*base76 + (16299179488297979/61875000000000000000000000000000 : ℝ)*base77 + (748474241090452021/61875000000000000000000000000000 : ℝ)*base80 + (3676671630139/1237500000000000000000000000 : ℝ)*base82 + (29901277/10000000000000000000000 : ℝ)*base90 + (29901277/10000000000000000000000 : ℝ)*base92 + (29901277/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23188969580832262683015031/2578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352351501/50000000000000 : ℝ)*(base19) + (1636214253/50000000000000 : ℝ)*(base23) + (105696021/25000000000000 : ℝ)*(upper2) + (20927961/100000000000000 : ℝ)*(upper3) + (985677561/100000000000000 : ℝ)*(upper5) + (2281107762588679/50000000000000 : ℝ)*(major0) + (2281107762588679/50000000000000 : ℝ)*(major1) + (2281107762588679/50000000000000 : ℝ)*(major2) + (21546876559/100000000000000 : ℝ)*(sp1) + (48903122283/100000000000000 : ℝ)*(sp2) + (6242884670354987/100000000000000 : ℝ)*(sp4) + (249714496751017/4000000000000 : ℝ)*(sp5) + (3121416247402099/50000000000000 : ℝ)*(sp6) + (144077304009137/5000000000000 : ℝ)*(sp7) + (144077304009137/5000000000000 : ℝ)*(f.failure) + (6242884670354987/100000000000000 : ℝ)*(f.sum) + (11843443651859/2475000000000000000000000000 : ℝ)*base65 + (164888943916353719/30937500000000000000000000000000 : ℝ)*base67 + (149995038715728719/30937500000000000000000000000000 : ℝ)*base69 + (180730048292291219/30937500000000000000000000000000 : ℝ)*base71 + (4793475075659/2475000000000000000000000000 : ℝ)*base73 + (69892843610103719/30937500000000000000000000000000 : ℝ)*base75 + (109155925386978719/30937500000000000000000000000000 : ℝ)*base77 + (68976506710833781/30937500000000000000000000000000 : ℝ)*base80 + (5564471466667/1237500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4035421/500000000000000000000 : ℝ)*base90 + (4035421/500000000000000000000 : ℝ)*base92 + (4035421/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1433_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1433_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1433_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1433_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
