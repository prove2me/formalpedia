-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:46:40.836917+00:00
-- url     : https://prove2.me/submissions/4d3fffaa-e19e-4381-9836-9c2efaa206e1

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
theorem support_rectangle_w1403_s0_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-221703587/1250000000 : ℝ)*x 0 + (2985492167/5000000000 : ℝ)*x 1 + (60315663/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221703587/1250000000 : ℝ)^4363 ≤ (10435299988249/100000000000000 : ℝ)^3339 := by
    have hnat : (221703587 : ℕ)^4363*100000000000000^3339 ≤ 10435299988249^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221703587 1250000000 10435299988249 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2985492167/5000000000 : ℝ)^4363 ≤ (50975794253163/100000000000000 : ℝ)^3339 := by
    have hnat : (2985492167 : ℕ)^4363*100000000000000^3339 ≤ 50975794253163^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985492167 5000000000 50975794253163 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60315663/125000000 : ℝ)^4363 ≤ (38588905743501/100000000000000 : ℝ)^3339 := by
    have hnat : (60315663 : ℕ)^4363*100000000000000^3339 ≤ 38588905743501^3339*125000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60315663 125000000 38588905743501 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221703587/1250000000 : ℝ), (2985492167/5000000000 : ℝ), (60315663/125000000 : ℝ)] ![(10435299988249/100000000000000 : ℝ), (50975794253163/100000000000000 : ℝ), (38588905743501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221703587/1250000000 : ℝ)|^4363 ≤ (10435299988249/100000000000000 : ℝ)^3339
        have hw : |(-221703587/1250000000 : ℝ)|=(221703587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2985492167/5000000000 : ℝ)|^4363 ≤ (50975794253163/100000000000000 : ℝ)^3339
        have hw : |(2985492167/5000000000 : ℝ)|=(2985492167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60315663/125000000 : ℝ)|^4363 ≤ (38588905743501/100000000000000 : ℝ)^3339
        have hw : |(60315663/125000000 : ℝ)|=(60315663/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (219799791/400000000 : ℝ)*x 0 + (-1211012007/5000000000 : ℝ)*x 1 + (4825253297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219799791/400000000 : ℝ)^4363 ≤ (45732063980101/100000000000000 : ℝ)^3339 := by
    have hnat : (219799791 : ℕ)^4363*100000000000000^3339 ≤ 45732063980101^3339*400000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219799791 400000000 45732063980101 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211012007/5000000000 : ℝ)^4363 ≤ (15679027573641/100000000000000 : ℝ)^3339 := by
    have hnat : (1211012007 : ℕ)^4363*100000000000000^3339 ≤ 15679027573641^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211012007 5000000000 15679027573641 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4825253297/10000000000 : ℝ)^4363 ≤ (38588908429119/100000000000000 : ℝ)^3339 := by
    have hnat : (4825253297 : ℕ)^4363*100000000000000^3339 ≤ 38588908429119^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825253297 10000000000 38588908429119 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219799791/400000000 : ℝ), (-1211012007/5000000000 : ℝ), (4825253297/10000000000 : ℝ)] ![(45732063980101/100000000000000 : ℝ), (15679027573641/100000000000000 : ℝ), (38588908429119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219799791/400000000 : ℝ)|^4363 ≤ (45732063980101/100000000000000 : ℝ)^3339
        have hw : |(219799791/400000000 : ℝ)|=(219799791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1211012007/5000000000 : ℝ)|^4363 ≤ (15679027573641/100000000000000 : ℝ)^3339
        have hw : |(-1211012007/5000000000 : ℝ)|=(1211012007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4825253297/10000000000 : ℝ)|^4363 ≤ (38588908429119/100000000000000 : ℝ)^3339
        have hw : |(4825253297/10000000000 : ℝ)|=(4825253297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2747497479/5000000000 : ℝ)*x 0 + (965050639/2000000000 : ℝ)*x 1 + (-1211011953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747497479/5000000000 : ℝ)^4363 ≤ (22866032985097/50000000000000 : ℝ)^3339 := by
    have hnat : (2747497479 : ℕ)^4363*50000000000000^3339 ≤ 22866032985097^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747497479 5000000000 22866032985097 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965050639/2000000000 : ℝ)^4363 ≤ (1205903355101/3125000000000 : ℝ)^3339 := by
    have hnat : (965050639 : ℕ)^4363*3125000000000^3339 ≤ 1205903355101^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965050639 2000000000 1205903355101 3125000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211011953/5000000000 : ℝ)^4363 ≤ (15679026660089/100000000000000 : ℝ)^3339 := by
    have hnat : (1211011953 : ℕ)^4363*100000000000000^3339 ≤ 15679026660089^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211011953 5000000000 15679026660089 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747497479/5000000000 : ℝ), (965050639/2000000000 : ℝ), (-1211011953/5000000000 : ℝ)] ![(22866032985097/50000000000000 : ℝ), (1205903355101/3125000000000 : ℝ), (15679026660089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747497479/5000000000 : ℝ)|^4363 ≤ (22866032985097/50000000000000 : ℝ)^3339
        have hw : |(2747497479/5000000000 : ℝ)|=(2747497479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965050639/2000000000 : ℝ)|^4363 ≤ (1205903355101/3125000000000 : ℝ)^3339
        have hw : |(965050639/2000000000 : ℝ)|=(965050639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1211011953/5000000000 : ℝ)|^4363 ≤ (15679026660089/100000000000000 : ℝ)^3339
        have hw : |(-1211011953/5000000000 : ℝ)|=(1211011953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169753299/10000000000 : ℝ)*x 0 + (1552045269/5000000000 : ℝ)*x 1 + (1389774807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169753299/10000000000 : ℝ)^4363 ≤ (15943230502607/50000000000000 : ℝ)^3339 := by
    have hnat : (4169753299 : ℕ)^4363*50000000000000^3339 ≤ 15943230502607^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169753299 10000000000 15943230502607 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552045269/5000000000 : ℝ)^4363 ≤ (21683106523763/100000000000000 : ℝ)^3339 := by
    have hnat : (1552045269 : ℕ)^4363*100000000000000^3339 ≤ 21683106523763^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552045269 5000000000 21683106523763 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389774807/2500000000 : ℝ)^4363 ≤ (46430432452857/100000000000000 : ℝ)^3339 := by
    have hnat : (1389774807 : ℕ)^4363*100000000000000^3339 ≤ 46430432452857^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389774807 2500000000 46430432452857 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169753299/10000000000 : ℝ), (1552045269/5000000000 : ℝ), (1389774807/2500000000 : ℝ)] ![(15943230502607/50000000000000 : ℝ), (21683106523763/100000000000000 : ℝ), (46430432452857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169753299/10000000000 : ℝ)|^4363 ≤ (15943230502607/50000000000000 : ℝ)^3339
        have hw : |(4169753299/10000000000 : ℝ)|=(4169753299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552045269/5000000000 : ℝ)|^4363 ≤ (21683106523763/100000000000000 : ℝ)^3339
        have hw : |(1552045269/5000000000 : ℝ)|=(1552045269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389774807/2500000000 : ℝ)|^4363 ≤ (46430432452857/100000000000000 : ℝ)^3339
        have hw : |(1389774807/2500000000 : ℝ)|=(1389774807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777773501/10000000000 : ℝ)*x 0 + (2427311967/5000000000 : ℝ)*x 1 + (5940564191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777773501/10000000000 : ℝ)^4363 ≤ (10467176489103/100000000000000 : ℝ)^3339 := by
    have hnat : (1777773501 : ℕ)^4363*100000000000000^3339 ≤ 10467176489103^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777773501 10000000000 10467176489103 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2427311967/5000000000 : ℝ)^4363 ≤ (38896114031097/100000000000000 : ℝ)^3339 := by
    have hnat : (2427311967 : ℕ)^4363*100000000000000^3339 ≤ 38896114031097^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427311967 5000000000 38896114031097 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5940564191/10000000000 : ℝ)^4363 ≤ (50636709466317/100000000000000 : ℝ)^3339 := by
    have hnat : (5940564191 : ℕ)^4363*100000000000000^3339 ≤ 50636709466317^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5940564191 10000000000 50636709466317 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777773501/10000000000 : ℝ), (2427311967/5000000000 : ℝ), (5940564191/10000000000 : ℝ)] ![(10467176489103/100000000000000 : ℝ), (38896114031097/100000000000000 : ℝ), (50636709466317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777773501/10000000000 : ℝ)|^4363 ≤ (10467176489103/100000000000000 : ℝ)^3339
        have hw : |(-1777773501/10000000000 : ℝ)|=(1777773501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2427311967/5000000000 : ℝ)|^4363 ≤ (38896114031097/100000000000000 : ℝ)^3339
        have hw : |(2427311967/5000000000 : ℝ)|=(2427311967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5940564191/10000000000 : ℝ)|^4363 ≤ (50636709466317/100000000000000 : ℝ)^3339
        have hw : |(5940564191/10000000000 : ℝ)|=(5940564191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518240403/1000000000 : ℝ)*x 0 + (-653356627/5000000000 : ℝ)*x 1 + (5940564413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518240403/1000000000 : ℝ)^4363 ≤ (42362746040859/100000000000000 : ℝ)^3339 := by
    have hnat : (518240403 : ℕ)^4363*100000000000000^3339 ≤ 42362746040859^3339*1000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518240403 1000000000 42362746040859 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653356627/5000000000 : ℝ)^4363 ≤ (7000542005103/100000000000000 : ℝ)^3339 := by
    have hnat : (653356627 : ℕ)^4363*100000000000000^3339 ≤ 7000542005103^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653356627 5000000000 7000542005103 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5940564413/10000000000 : ℝ)^4363 ≤ (50636711938949/100000000000000 : ℝ)^3339 := by
    have hnat : (5940564413 : ℕ)^4363*100000000000000^3339 ≤ 50636711938949^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5940564413 10000000000 50636711938949 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518240403/1000000000 : ℝ), (-653356627/5000000000 : ℝ), (5940564413/10000000000 : ℝ)] ![(42362746040859/100000000000000 : ℝ), (7000542005103/100000000000000 : ℝ), (50636711938949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518240403/1000000000 : ℝ)|^4363 ≤ (42362746040859/100000000000000 : ℝ)^3339
        have hw : |(518240403/1000000000 : ℝ)|=(518240403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-653356627/5000000000 : ℝ)|^4363 ≤ (7000542005103/100000000000000 : ℝ)^3339
        have hw : |(-653356627/5000000000 : ℝ)|=(653356627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5940564413/10000000000 : ℝ)|^4363 ≤ (50636711938949/100000000000000 : ℝ)^3339
        have hw : |(5940564413/10000000000 : ℝ)|=(5940564413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5182404383/10000000000 : ℝ)*x 0 + (297028213/500000000 : ℝ)*x 1 + (-1306712959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182404383/10000000000 : ℝ)^4363 ≤ (5295343726417/12500000000000 : ℝ)^3339 := by
    have hnat : (5182404383 : ℕ)^4363*12500000000000^3339 ≤ 5295343726417^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182404383 10000000000 5295343726417 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297028213/500000000 : ℝ)^4363 ≤ (25318355117419/50000000000000 : ℝ)^3339 := by
    have hnat : (297028213 : ℕ)^4363*50000000000000^3339 ≤ 25318355117419^3339*500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297028213 500000000 25318355117419 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306712959/10000000000 : ℝ)^4363 ≤ (3500269969999/50000000000000 : ℝ)^3339 := by
    have hnat : (1306712959 : ℕ)^4363*50000000000000^3339 ≤ 3500269969999^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306712959 10000000000 3500269969999 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182404383/10000000000 : ℝ), (297028213/500000000 : ℝ), (-1306712959/10000000000 : ℝ)] ![(5295343726417/12500000000000 : ℝ), (25318355117419/50000000000000 : ℝ), (3500269969999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182404383/10000000000 : ℝ)|^4363 ≤ (5295343726417/12500000000000 : ℝ)^3339
        have hw : |(5182404383/10000000000 : ℝ)|=(5182404383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297028213/500000000 : ℝ)|^4363 ≤ (25318355117419/50000000000000 : ℝ)^3339
        have hw : |(297028213/500000000 : ℝ)|=(297028213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306712959/10000000000 : ℝ)|^4363 ≤ (3500269969999/50000000000000 : ℝ)^3339
        have hw : |(-1306712959/10000000000 : ℝ)|=(1306712959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s0_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4178634897/10000000000 : ℝ)*x 0 + (2748082437/5000000000 : ℝ)*x 1 + (3169273217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178634897/10000000000 : ℝ)^4363 ≤ (31975237423537/100000000000000 : ℝ)^3339 := by
    have hnat : (4178634897 : ℕ)^4363*100000000000000^3339 ≤ 31975237423537^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178634897 10000000000 31975237423537 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748082437/5000000000 : ℝ)^4363 ≤ (9148957803693/20000000000000 : ℝ)^3339 := by
    have hnat : (2748082437 : ℕ)^4363*20000000000000^3339 ≤ 9148957803693^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748082437 5000000000 9148957803693 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169273217/10000000000 : ℝ)^4363 ≤ (22279973547299/100000000000000 : ℝ)^3339 := by
    have hnat : (3169273217 : ℕ)^4363*100000000000000^3339 ≤ 22279973547299^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169273217 10000000000 22279973547299 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178634897/10000000000 : ℝ), (2748082437/5000000000 : ℝ), (3169273217/10000000000 : ℝ)] ![(31975237423537/100000000000000 : ℝ), (9148957803693/20000000000000 : ℝ), (22279973547299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178634897/10000000000 : ℝ)|^4363 ≤ (31975237423537/100000000000000 : ℝ)^3339
        have hw : |(4178634897/10000000000 : ℝ)|=(4178634897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748082437/5000000000 : ℝ)|^4363 ≤ (9148957803693/20000000000000 : ℝ)^3339
        have hw : |(2748082437/5000000000 : ℝ)|=(2748082437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169273217/10000000000 : ℝ)|^4363 ≤ (22279973547299/100000000000000 : ℝ)^3339
        have hw : |(3169273217/10000000000 : ℝ)|=(3169273217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (931/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26439/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2181/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2181 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2181*1^512 ≤ 0^512*1^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2181/512 : ℝ) ≤ (1008878424755213403/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2181 ≤ (1008878424755213403/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2181*50000000000000000000^512 ≤ 1008878424755213403^512*5^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1008878424755213403 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1008878424755213403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2181 := by
      have hnat : (1 : ℕ)^512*1^2181 ≤ 1^2181*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51008878424755213403/50000000000000000000 : ℝ) ≤ (10047006374480221/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (51008878424755213403/50000000000000000000 : ℝ)^512 ≤ (10047006374480221/10000000000000000 : ℝ)^2181 := by
      have hnat : (51008878424755213403 : ℕ)^512*10000000000000000^2181 ≤ 10047006374480221^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51008878424755213403 50000000000000000000 10047006374480221 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047006374480221/10000000000000000 : ℝ)) (X := (51008878424755213403/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26008878424755213403/25000000000000000000 : ℝ) ≤ (5047006374480221/5000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (26008878424755213403/25000000000000000000 : ℝ)^512 ≤ (5047006374480221/5000000000000000 : ℝ)^2181 := by
      have hnat : (26008878424755213403 : ℕ)^512*5000000000000000^2181 ≤ 5047006374480221^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26008878424755213403 25000000000000000000 5047006374480221 5000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047006374480221/5000000000000000 : ℝ)) (X := (26008878424755213403/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47006374480221/4000000000000000 : ℝ)*(0 : ℝ))^(2181/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(47006374480221/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1008878424755213403/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47006374480221/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (1 : ℝ)+(47006374480221/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047006374480221/10000000000000000 : ℝ) by norm_num, show 1+(1008878424755213403/50000000000000000000 : ℝ)+(0 : ℝ)=(51008878424755213403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1008878424755213403/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47006374480221/4000000000000000 : ℝ)*(2/5 : ℝ))^(2181/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(47006374480221/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047006374480221/5000000000000000 : ℝ) by norm_num, show 1+2*(1008878424755213403/50000000000000000000 : ℝ)=(26008878424755213403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47006374480221/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47006374480221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47006374480221/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47006374480221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47006374480221/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47006374480221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-221703587/1250000000 : ℝ)*X 0 0+(2985492167/5000000000 : ℝ)*X 0 1+(60315663/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((219799791/400000000 : ℝ)*X 1 0+(-1211012007/5000000000 : ℝ)*X 1 1+(4825253297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2747497479/5000000000 : ℝ)*X 2 0+(965050639/2000000000 : ℝ)*X 2 1+(-1211011953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169753299/10000000000 : ℝ)*X 0 0+(1552045269/5000000000 : ℝ)*X 0 1+(1389774807/2500000000 : ℝ)*X 0 2+(4169753299/10000000000 : ℝ)*X 1 0+(1552045269/5000000000 : ℝ)*X 1 1+(1389774807/2500000000 : ℝ)*X 1 2+(4169753299/10000000000 : ℝ)*X 2 0+(1552045269/5000000000 : ℝ)*X 2 1+(1389774807/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1777773501/10000000000 : ℝ)*X 0 0+(2427311967/5000000000 : ℝ)*X 0 1+(5940564191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518240403/1000000000 : ℝ)*X 1 0+(-653356627/5000000000 : ℝ)*X 1 1+(5940564413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182404383/10000000000 : ℝ)*X 2 0+(297028213/500000000 : ℝ)*X 2 1+(-1306712959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4178634897/10000000000 : ℝ)*X 0 0+(2748082437/5000000000 : ℝ)*X 0 1+(3169273217/10000000000 : ℝ)*X 0 2+(4178634897/10000000000 : ℝ)*X 1 0+(2748082437/5000000000 : ℝ)*X 1 1+(3169273217/10000000000 : ℝ)*X 1 2+(4178634897/10000000000 : ℝ)*X 2 0+(2748082437/5000000000 : ℝ)*X 2 1+(3169273217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (754577137888483758701169/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2451963/12500000000000 : ℝ)*(base1) + (176817079/10000000000000 : ℝ)*(base19) + (898619097/50000000000000 : ℝ)*(base23) + (8117/3906250000 : ℝ)*(upper3) + (245471083/100000000000000 : ℝ)*(upper5) + (320038488014621/50000000000000 : ℝ)*(major0) + (320038488014621/50000000000000 : ℝ)*(major1) + (320038488014621/50000000000000 : ℝ)*(major2) + (218202710741857/25000000000000 : ℝ)*(sp0) + (436407756082923/50000000000000 : ℝ)*(sp1) + (436407741549221/50000000000000 : ℝ)*(sp2) + (407333432913927/100000000000000 : ℝ)*(sp3) + (6456984911/100000000000000 : ℝ)*(sp4) + (5935333/200000000000 : ℝ)*(sp7) + (40733642019613/10000000000000 : ℝ)*(f.failure) + (218204320084159/25000000000000 : ℝ)*(f.sum) + (67291714088759/100000000000000000000000000000 : ℝ)*base66 + (1143728187088759/200000000000000000000000000000 : ℝ)*base68 + (293710727911241/200000000000000000000000000000 : ℝ)*base69 + (84427058711241/200000000000000000000000000000 : ℝ)*base71 + (550354664888759/100000000000000000000000000000 : ℝ)*base74 + (372367500288759/200000000000000000000000000000 : ℝ)*base76 + (23586901511241/200000000000000000000000000000 : ℝ)*base77 + (880186059888759/200000000000000000000000000000 : ℝ)*base80 + (138945317088759/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2429821/1000000000000000000000 : ℝ)*base90 + (2429821/1000000000000000000000 : ℝ)*base92 + (2429821/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7278852956760250001613/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2042838093/100000000000000 : ℝ)*(base19) + (266752097/12500000000000 : ℝ)*(base23) + (84342391/100000000000000 : ℝ)*(base32) + (962937/312500000000 : ℝ)*(upper3) + (118049773/50000000000000 : ℝ)*(upper5) + (10551708862309/1562500000000 : ℝ)*(major0) + (10551708862309/1562500000000 : ℝ)*(major1) + (10551708862309/1562500000000 : ℝ)*(major2) + (1213966719/25000000000000 : ℝ)*(sp1) + (2663805177/50000000000000 : ℝ)*(sp2) + (184172116292561/20000000000000 : ℝ)*(sp4) + (230213420689459/25000000000000 : ℝ)*(sp5) + (36834124793427/4000000000000 : ℝ)*(sp6) + (214878879002979/50000000000000 : ℝ)*(sp7) + (429757842348349/100000000000000 : ℝ)*(f.failure) + (184172116292561/20000000000000 : ℝ)*(f.sum) + (919556053167/390625000000000000000000000 : ℝ)*base66 + (27248955622211/6250000000000000000000000000 : ℝ)*base68 + (60193633615961/6250000000000000000000000000 : ℝ)*base70 + (34890669022211/6250000000000000000000000000 : ℝ)*base72 + (7115869247211/3125000000000000000000000000 : ℝ)*base74 + (45625912897211/6250000000000000000000000000 : ℝ)*base76 + (17780085753461/6250000000000000000000000000 : ℝ)*base78 + (30047590997211/6250000000000000000000000000 : ℝ)*base80 + (1165853381271/195312500000000000000000000 : ℝ)*base82 + (66560867/10000000000000000000000 : ℝ)*base89 + (66560867/10000000000000000000000 : ℝ)*base91 + (66560867/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1403_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (931/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26439/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_s1_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949681203/10000000000 : ℝ)*x 0 + (2807915681/5000000000 : ℝ)*x 1 + (1013516893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949681203/10000000000 : ℝ)^4363 ≤ (5904465759427/50000000000000 : ℝ)^3339 := by
    have hnat : (1949681203 : ℕ)^4363*50000000000000^3339 ≤ 5904465759427^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949681203 10000000000 5904465759427 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807915681/5000000000 : ℝ)^4363 ≤ (47050549551181/100000000000000 : ℝ)^3339 := by
    have hnat : (2807915681 : ℕ)^4363*100000000000000^3339 ≤ 47050549551181^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807915681 5000000000 47050549551181 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013516893/2000000000 : ℝ)^4363 ≤ (41140518911777/100000000000000 : ℝ)^3339 := by
    have hnat : (1013516893 : ℕ)^4363*100000000000000^3339 ≤ 41140518911777^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013516893 2000000000 41140518911777 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949681203/10000000000 : ℝ), (2807915681/5000000000 : ℝ), (1013516893/2000000000 : ℝ)] ![(5904465759427/50000000000000 : ℝ), (47050549551181/100000000000000 : ℝ), (41140518911777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949681203/10000000000 : ℝ)|^4363 ≤ (5904465759427/50000000000000 : ℝ)^3339
        have hw : |(-1949681203/10000000000 : ℝ)|=(1949681203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807915681/5000000000 : ℝ)|^4363 ≤ (47050549551181/100000000000000 : ℝ)^3339
        have hw : |(2807915681/5000000000 : ℝ)|=(2807915681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013516893/2000000000 : ℝ)|^4363 ≤ (41140518911777/100000000000000 : ℝ)^3339
        have hw : |(1013516893/2000000000 : ℝ)|=(1013516893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399437263/10000000000 : ℝ)*x 0 + (-560194163/2500000000 : ℝ)*x 1 + (63344817/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399437263/10000000000 : ℝ)^4363 ≤ (5586959363081/12500000000000 : ℝ)^3339 := by
    have hnat : (5399437263 : ℕ)^4363*12500000000000^3339 ≤ 5586959363081^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399437263 10000000000 5586959363081 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560194163/2500000000 : ℝ)^4363 ≤ (1416379667367/10000000000000 : ℝ)^3339 := by
    have hnat : (560194163 : ℕ)^4363*10000000000000^3339 ≤ 1416379667367^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560194163 2500000000 1416379667367 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63344817/125000000 : ℝ)^4363 ≤ (20570264203013/50000000000000 : ℝ)^3339 := by
    have hnat : (63344817 : ℕ)^4363*50000000000000^3339 ≤ 20570264203013^3339*125000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63344817 125000000 20570264203013 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399437263/10000000000 : ℝ), (-560194163/2500000000 : ℝ), (63344817/125000000 : ℝ)] ![(5586959363081/12500000000000 : ℝ), (1416379667367/10000000000000 : ℝ), (20570264203013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399437263/10000000000 : ℝ)|^4363 ≤ (5586959363081/12500000000000 : ℝ)^3339
        have hw : |(5399437263/10000000000 : ℝ)|=(5399437263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560194163/2500000000 : ℝ)|^4363 ≤ (1416379667367/10000000000000 : ℝ)^3339
        have hw : |(-560194163/2500000000 : ℝ)|=(560194163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63344817/125000000 : ℝ)|^4363 ≤ (20570264203013/50000000000000 : ℝ)^3339
        have hw : |(63344817/125000000 : ℝ)|=(63344817/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699718979/5000000000 : ℝ)*x 0 + (5067584797/10000000000 : ℝ)*x 1 + (-1120388233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699718979/5000000000 : ℝ)^4363 ≤ (44695682422099/100000000000000 : ℝ)^3339 := by
    have hnat : (2699718979 : ℕ)^4363*100000000000000^3339 ≤ 44695682422099^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699718979 5000000000 44695682422099 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5067584797/10000000000 : ℝ)^4363 ≤ (20570261216833/50000000000000 : ℝ)^3339 := by
    have hnat : (5067584797 : ℕ)^4363*50000000000000^3339 ≤ 20570261216833^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067584797 10000000000 20570261216833 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120388233/5000000000 : ℝ)^4363 ≤ (14163795137417/100000000000000 : ℝ)^3339 := by
    have hnat : (1120388233 : ℕ)^4363*100000000000000^3339 ≤ 14163795137417^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120388233 5000000000 14163795137417 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699718979/5000000000 : ℝ), (5067584797/10000000000 : ℝ), (-1120388233/5000000000 : ℝ)] ![(44695682422099/100000000000000 : ℝ), (20570261216833/50000000000000 : ℝ), (14163795137417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699718979/5000000000 : ℝ)|^4363 ≤ (44695682422099/100000000000000 : ℝ)^3339
        have hw : |(2699718979/5000000000 : ℝ)|=(2699718979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5067584797/10000000000 : ℝ)|^4363 ≤ (20570261216833/50000000000000 : ℝ)^3339
        have hw : |(5067584797/10000000000 : ℝ)|=(5067584797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120388233/5000000000 : ℝ)|^4363 ≤ (14163795137417/100000000000000 : ℝ)^3339
        have hw : |(-1120388233/5000000000 : ℝ)|=(1120388233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535168899/1250000000 : ℝ)*x 0 + (3730344083/10000000000 : ℝ)*x 1 + (2452547567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535168899/1250000000 : ℝ)^4363 ≤ (8251531793477/25000000000000 : ℝ)^3339 := by
    have hnat : (535168899 : ℕ)^4363*25000000000000^3339 ≤ 8251531793477^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535168899 1250000000 8251531793477 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3730344083/10000000000 : ℝ)^4363 ≤ (27568518141197/100000000000000 : ℝ)^3339 := by
    have hnat : (3730344083 : ℕ)^4363*100000000000000^3339 ≤ 27568518141197^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730344083 10000000000 27568518141197 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2452547567/5000000000 : ℝ)^4363 ≤ (19712677339227/50000000000000 : ℝ)^3339 := by
    have hnat : (2452547567 : ℕ)^4363*50000000000000^3339 ≤ 19712677339227^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452547567 5000000000 19712677339227 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535168899/1250000000 : ℝ), (3730344083/10000000000 : ℝ), (2452547567/5000000000 : ℝ)] ![(8251531793477/25000000000000 : ℝ), (27568518141197/100000000000000 : ℝ), (19712677339227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535168899/1250000000 : ℝ)|^4363 ≤ (8251531793477/25000000000000 : ℝ)^3339
        have hw : |(535168899/1250000000 : ℝ)|=(535168899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3730344083/10000000000 : ℝ)|^4363 ≤ (27568518141197/100000000000000 : ℝ)^3339
        have hw : |(3730344083/10000000000 : ℝ)|=(3730344083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2452547567/5000000000 : ℝ)|^4363 ≤ (19712677339227/50000000000000 : ℝ)^3339
        have hw : |(2452547567/5000000000 : ℝ)|=(2452547567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121882273/625000000 : ℝ)*x 0 + (5074145813/10000000000 : ℝ)*x 1 + (87643069/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121882273/625000000 : ℝ)^4363 ≤ (11812375689129/100000000000000 : ℝ)^3339 := by
    have hnat : (121882273 : ℕ)^4363*100000000000000^3339 ≤ 11812375689129^3339*625000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121882273 625000000 11812375689129 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074145813/10000000000 : ℝ)^4363 ≤ (20605068077807/50000000000000 : ℝ)^3339 := by
    have hnat : (5074145813 : ℕ)^4363*50000000000000^3339 ≤ 20605068077807^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074145813 10000000000 20605068077807 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87643069/156250000 : ℝ)^4363 ≤ (9395497629549/20000000000000 : ℝ)^3339 := by
    have hnat : (87643069 : ℕ)^4363*20000000000000^3339 ≤ 9395497629549^3339*156250000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87643069 156250000 9395497629549 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121882273/625000000 : ℝ), (5074145813/10000000000 : ℝ), (87643069/156250000 : ℝ)] ![(11812375689129/100000000000000 : ℝ), (20605068077807/50000000000000 : ℝ), (9395497629549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121882273/625000000 : ℝ)|^4363 ≤ (11812375689129/100000000000000 : ℝ)^3339
        have hw : |(-121882273/625000000 : ℝ)|=(121882273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074145813/10000000000 : ℝ)|^4363 ≤ (20605068077807/50000000000000 : ℝ)^3339
        have hw : |(5074145813/10000000000 : ℝ)|=(5074145813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87643069/156250000 : ℝ)|^4363 ≤ (9395497629549/20000000000000 : ℝ)^3339
        have hw : |(87643069/156250000 : ℝ)|=(87643069/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262823811/500000000 : ℝ)*x 0 + (-212400693/1250000000 : ℝ)*x 1 + (5609156327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262823811/500000000 : ℝ)^4363 ≤ (21577828563587/50000000000000 : ℝ)^3339 := by
    have hnat : (262823811 : ℕ)^4363*50000000000000^3339 ≤ 21577828563587^3339*500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262823811 500000000 21577828563587 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212400693/1250000000 : ℝ)^4363 ≤ (4933427841057/50000000000000 : ℝ)^3339 := by
    have hnat : (212400693 : ℕ)^4363*50000000000000^3339 ≤ 4933427841057^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212400693 1250000000 4933427841057 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5609156327/10000000000 : ℝ)^4363 ≤ (23488743586881/50000000000000 : ℝ)^3339 := by
    have hnat : (5609156327 : ℕ)^4363*50000000000000^3339 ≤ 23488743586881^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609156327 10000000000 23488743586881 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262823811/500000000 : ℝ), (-212400693/1250000000 : ℝ), (5609156327/10000000000 : ℝ)] ![(21577828563587/50000000000000 : ℝ), (4933427841057/50000000000000 : ℝ), (23488743586881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262823811/500000000 : ℝ)|^4363 ≤ (21577828563587/50000000000000 : ℝ)^3339
        have hw : |(262823811/500000000 : ℝ)|=(262823811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212400693/1250000000 : ℝ)|^4363 ≤ (4933427841057/50000000000000 : ℝ)^3339
        have hw : |(-212400693/1250000000 : ℝ)|=(212400693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5609156327/10000000000 : ℝ)|^4363 ≤ (23488743586881/50000000000000 : ℝ)^3339
        have hw : |(5609156327/10000000000 : ℝ)|=(5609156327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256476779/10000000000 : ℝ)*x 0 + (5609156781/10000000000 : ℝ)*x 1 + (-849602049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256476779/10000000000 : ℝ)^4363 ≤ (4315566312403/10000000000000 : ℝ)^3339 := by
    have hnat : (5256476779 : ℕ)^4363*10000000000000^3339 ≤ 4315566312403^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256476779 10000000000 4315566312403 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5609156781/10000000000 : ℝ)^4363 ≤ (23488746071083/50000000000000 : ℝ)^3339 := by
    have hnat : (5609156781 : ℕ)^4363*50000000000000^3339 ≤ 23488746071083^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609156781 10000000000 23488746071083 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849602049/5000000000 : ℝ)^4363 ≤ (2466711177629/25000000000000 : ℝ)^3339 := by
    have hnat : (849602049 : ℕ)^4363*25000000000000^3339 ≤ 2466711177629^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849602049 5000000000 2466711177629 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256476779/10000000000 : ℝ), (5609156781/10000000000 : ℝ), (-849602049/5000000000 : ℝ)] ![(4315566312403/10000000000000 : ℝ), (23488746071083/50000000000000 : ℝ), (2466711177629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256476779/10000000000 : ℝ)|^4363 ≤ (4315566312403/10000000000000 : ℝ)^3339
        have hw : |(5256476779/10000000000 : ℝ)|=(5256476779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5609156781/10000000000 : ℝ)|^4363 ≤ (23488746071083/50000000000000 : ℝ)^3339
        have hw : |(5609156781/10000000000 : ℝ)|=(5609156781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-849602049/5000000000 : ℝ)|^4363 ≤ (2466711177629/25000000000000 : ℝ)^3339
        have hw : |(-849602049/5000000000 : ℝ)|=(849602049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s1_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070571319/2500000000 : ℝ)*x 0 + (4891035037/10000000000 : ℝ)*x 1 + (1872323047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070571319/2500000000 : ℝ)^4363 ≤ (33015537029753/100000000000000 : ℝ)^3339 := by
    have hnat : (1070571319 : ℕ)^4363*100000000000000^3339 ≤ 33015537029753^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070571319 2500000000 33015537029753 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4891035037/10000000000 : ℝ)^4363 ≤ (4909719000433/12500000000000 : ℝ)^3339 := by
    have hnat : (4891035037 : ℕ)^4363*12500000000000^3339 ≤ 4909719000433^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891035037 10000000000 4909719000433 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872323047/5000000000 : ℝ)^4363 ≤ (6926677738109/25000000000000 : ℝ)^3339 := by
    have hnat : (1872323047 : ℕ)^4363*25000000000000^3339 ≤ 6926677738109^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872323047 5000000000 6926677738109 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070571319/2500000000 : ℝ), (4891035037/10000000000 : ℝ), (1872323047/5000000000 : ℝ)] ![(33015537029753/100000000000000 : ℝ), (4909719000433/12500000000000 : ℝ), (6926677738109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070571319/2500000000 : ℝ)|^4363 ≤ (33015537029753/100000000000000 : ℝ)^3339
        have hw : |(1070571319/2500000000 : ℝ)|=(1070571319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4891035037/10000000000 : ℝ)|^4363 ≤ (4909719000433/12500000000000 : ℝ)^3339
        have hw : |(4891035037/10000000000 : ℝ)|=(4891035037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872323047/5000000000 : ℝ)|^4363 ≤ (6926677738109/25000000000000 : ℝ)^3339
        have hw : |(1872323047/5000000000 : ℝ)|=(1872323047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26439/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (931/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26439/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (931/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26439/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (931/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26439/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (931/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26439/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (931/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26439/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (931/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26439/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (931/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (931/50000 : ℝ) ^ (2181/512 : ℝ) ≤ (1067723753931/25000000000000000000 : ℝ) := by
    have hpowers : (931/50000 : ℝ)^2181 ≤ (1067723753931/25000000000000000000 : ℝ)^512 := by
      have hnat : (931 : ℕ)^2181*25000000000000000000^512 ≤ 1067723753931^512*50000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        931 50000 1067723753931 25000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (931/50000 : ℝ)) (X := (1067723753931/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26439/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (172929554035226183/50000000000000000000 : ℝ) := by
    have hpowers : (26439/100000 : ℝ)^2181 ≤ (172929554035226183/50000000000000000000 : ℝ)^512 := by
      have hnat : (26439 : ℕ)^2181*50000000000000000000^512 ≤ 172929554035226183^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26439 100000 172929554035226183 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26439/100000 : ℝ)) (X := (172929554035226183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500001067723753931/12500000000000000000 : ℝ) ≤ (10000000200522529/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (12500001067723753931/12500000000000000000 : ℝ)^512 ≤ (10000000200522529/10000000000000000 : ℝ)^2181 := by
      have hnat : (12500001067723753931 : ℕ)^512*10000000000000000^2181 ≤ 10000000200522529^2181*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500001067723753931 12500000000000000000 10000000200522529 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000200522529/10000000000000000 : ℝ)) (X := (12500001067723753931/12500000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10034586337896546809/10000000000000000000 : ℝ) ≤ (1251013572810557/1250000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (10034586337896546809/10000000000000000000 : ℝ)^512 ≤ (1251013572810557/1250000000000000 : ℝ)^2181 := by
      have hnat : (10034586337896546809 : ℕ)^512*1250000000000000^2181 ≤ 1251013572810557^2181*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10034586337896546809 10000000000000000000 1251013572810557 1250000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251013572810557/1250000000000000 : ℝ)) (X := (10034586337896546809/10000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25172929554035226183/25000000000000000000 : ℝ) ≤ (10016216964446383/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25172929554035226183/25000000000000000000 : ℝ)^512 ≤ (10016216964446383/10000000000000000 : ℝ)^2181 := by
      have hnat : (25172929554035226183 : ℕ)^512*10000000000000000^2181 ≤ 10016216964446383^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25172929554035226183 25000000000000000000 10016216964446383 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016216964446383/10000000000000000 : ℝ)) (X := (25172929554035226183/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1067723753931/25000000000000000000 : ℝ) ≤ ((7021137408966170831/7022000000000000000 : ℝ)+2*(8108381961927/2457700000000000 : ℝ)*(931/50000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (7021137408966170831/7022000000000000000 : ℝ)+2*(8108381961927/2457700000000000 : ℝ)*(931/50000 : ℝ)=(10000000200522529/10000000000000000 : ℝ) by norm_num, show 1+2*(1067723753931/25000000000000000000 : ℝ)=(12500001067723753931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172929554035226183/50000000000000000000 : ℝ)+(1067723753931/25000000000000000000 : ℝ) ≤ ((7021137408966170831/7022000000000000000 : ℝ)+(8108381961927/2457700000000000 : ℝ)*((26439/100000 : ℝ)+(931/50000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (7021137408966170831/7022000000000000000 : ℝ)+(8108381961927/2457700000000000 : ℝ)*((26439/100000 : ℝ)+(931/50000 : ℝ))=(1251013572810557/1250000000000000 : ℝ) by norm_num, show 1+(172929554035226183/50000000000000000000 : ℝ)+(1067723753931/25000000000000000000 : ℝ)=(10034586337896546809/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172929554035226183/50000000000000000000 : ℝ) ≤ ((7021137408966170831/7022000000000000000 : ℝ)+2*(8108381961927/2457700000000000 : ℝ)*(26439/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (7021137408966170831/7022000000000000000 : ℝ)+2*(8108381961927/2457700000000000 : ℝ)*(26439/100000 : ℝ)=(10016216964446383/10000000000000000 : ℝ) by norm_num, show 1+2*(172929554035226183/50000000000000000000 : ℝ)=(25172929554035226183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7021137408966170831/7022000000000000000 : ℝ)*(X 1 0+X 2 0)+(8108381961927/2457700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (931/50000 : ℝ)) (hi := (26439/100000 : ℝ)) (c := (7021137408966170831/7022000000000000000 : ℝ)) (alpha := (8108381961927/2457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7021137408966170831/7022000000000000000 : ℝ)*(X 0 1+X 2 1)+(8108381961927/2457700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (931/50000 : ℝ)) (hi := (26439/100000 : ℝ)) (c := (7021137408966170831/7022000000000000000 : ℝ)) (alpha := (8108381961927/2457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7021137408966170831/7022000000000000000 : ℝ)*(X 0 2+X 1 2)+(8108381961927/2457700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (931/50000 : ℝ)) (hi := (26439/100000 : ℝ)) (c := (7021137408966170831/7022000000000000000 : ℝ)) (alpha := (8108381961927/2457700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1949681203/10000000000 : ℝ)*X 0 0+(2807915681/5000000000 : ℝ)*X 0 1+(1013516893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5399437263/10000000000 : ℝ)*X 1 0+(-560194163/2500000000 : ℝ)*X 1 1+(63344817/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2699718979/5000000000 : ℝ)*X 2 0+(5067584797/10000000000 : ℝ)*X 2 1+(-1120388233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535168899/1250000000 : ℝ)*X 0 0+(3730344083/10000000000 : ℝ)*X 0 1+(2452547567/5000000000 : ℝ)*X 0 2+(535168899/1250000000 : ℝ)*X 1 0+(3730344083/10000000000 : ℝ)*X 1 1+(2452547567/5000000000 : ℝ)*X 1 2+(535168899/1250000000 : ℝ)*X 2 0+(3730344083/10000000000 : ℝ)*X 2 1+(2452547567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-121882273/625000000 : ℝ)*X 0 0+(5074145813/10000000000 : ℝ)*X 0 1+(87643069/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262823811/500000000 : ℝ)*X 1 0+(-212400693/1250000000 : ℝ)*X 1 1+(5609156327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256476779/10000000000 : ℝ)*X 2 0+(5609156781/10000000000 : ℝ)*X 2 1+(-849602049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070571319/2500000000 : ℝ)*X 0 0+(4891035037/10000000000 : ℝ)*X 0 1+(1872323047/5000000000 : ℝ)*X 0 2+(1070571319/2500000000 : ℝ)*X 1 0+(4891035037/10000000000 : ℝ)*X 1 1+(1872323047/5000000000 : ℝ)*X 1 2+(1070571319/2500000000 : ℝ)*X 2 0+(4891035037/10000000000 : ℝ)*X 2 1+(1872323047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22075507078303645601780181849/2457700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15852201/50000000000000 : ℝ)*(base1) + (853368859/50000000000000 : ℝ)*(base19) + (388304129/20000000000000 : ℝ)*(base23) + (27618181/20000000000000 : ℝ)*(upper3) + (68388713/25000000000000 : ℝ)*(upper5) + (1337640736625701/100000000000000 : ℝ)*(major0) + (1337640736625701/100000000000000 : ℝ)*(major1) + (1337640736625701/100000000000000 : ℝ)*(major2) + (456002208187539/25000000000000 : ℝ)*(sp0) + (1824022806470093/100000000000000 : ℝ)*(sp1) + (364804514337433/20000000000000 : ℝ)*(sp2) + (212812635326507/25000000000000 : ℝ)*(sp3) + (15712162057/100000000000000 : ℝ)*(sp4) + (608762711/10000000000000 : ℝ)*(sp7) + (42562833031877/5000000000000 : ℝ)*(f.failure) + (182402451320781/10000000000000 : ℝ)*(f.sum) + (454865271245407/122885000000000000000000000000 : ℝ)*base65 + (2219764131073367283/4915400000000000000000000000000000 : ℝ)*base68 + (890135044516832717/4915400000000000000000000000000000 : ℝ)*base69 + (1749431258711432717/4915400000000000000000000000000000 : ℝ)*base71 + (4622101621003/122885000000000000000000000000 : ℝ)*base74 + (6676652497794367283/4915400000000000000000000000000000 : ℝ)*base76 + (15693764307202032717/4915400000000000000000000000000000 : ℝ)*base77 + (14911286239469832717/4915400000000000000000000000000000 : ℝ)*base79 + (120843428818057/122885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4017509/500000000000000000000 : ℝ)*base90 + (4017509/500000000000000000000 : ℝ)*base92 + (4017509/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4229736798495847179344990481/491540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31944377/12500000000000 : ℝ)*(base1) + (204497283/10000000000000 : ℝ)*(base19) + (588885687/25000000000000 : ℝ)*(base23) + (186811761/100000000000000 : ℝ)*(upper3) + (12857227/4000000000000 : ℝ)*(upper5) + (274142866194531/20000000000000 : ℝ)*(major0) + (274142866194531/20000000000000 : ℝ)*(major1) + (274142866194531/20000000000000 : ℝ)*(major2) + (10176391711/100000000000000 : ℝ)*(sp1) + (14287038703/100000000000000 : ℝ)*(sp2) + (934562188635259/50000000000000 : ℝ)*(sp4) + (23363898754387/1250000000000 : ℝ)*(sp5) + (1869107479134051/100000000000000 : ℝ)*(sp6) + (436151998919537/50000000000000 : ℝ)*(sp7) + (87230425339409/10000000000000 : ℝ)*(f.failure) + (934562060857751/50000000000000 : ℝ)*(f.sum) + (6113746235363/24577000000000000000000000000 : ℝ)*base66 + (4724682876133543173/983080000000000000000000000000000 : ℝ)*base68 + (6963887026895303173/983080000000000000000000000000000 : ℝ)*base70 + (4154696482871856827/983080000000000000000000000000000 : ℝ)*base71 + (4844151154813/4915400000000000000000000000 : ℝ)*base74 + (422846924257336827/983080000000000000000000000000000 : ℝ)*base75 + (4055095050318943173/983080000000000000000000000000000 : ℝ)*base78 + (7054589345896583173/983080000000000000000000000000000 : ℝ)*base80 + (39010959270483/24577000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (855153/1000000000000000000000 : ℝ)*base90 + (855153/1000000000000000000000 : ℝ)*base92 + (855153/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1403_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26439/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (931/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_s2_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984798537/10000000000 : ℝ)*x 0 + (5464184773/10000000000 : ℝ)*x 1 + (5196659263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984798537/10000000000 : ℝ)^4363 ≤ (12087627190659/100000000000000 : ℝ)^3339 := by
    have hnat : (1984798537 : ℕ)^4363*100000000000000^3339 ≤ 12087627190659^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984798537 10000000000 12087627190659 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464184773/10000000000 : ℝ)^4363 ≤ (22698649506403/50000000000000 : ℝ)^3339 := by
    have hnat : (5464184773 : ℕ)^4363*50000000000000^3339 ≤ 22698649506403^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464184773 10000000000 22698649506403 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196659263/10000000000 : ℝ)^4363 ≤ (42515073772973/100000000000000 : ℝ)^3339 := by
    have hnat : (5196659263 : ℕ)^4363*100000000000000^3339 ≤ 42515073772973^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196659263 10000000000 42515073772973 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984798537/10000000000 : ℝ), (5464184773/10000000000 : ℝ), (5196659263/10000000000 : ℝ)] ![(12087627190659/100000000000000 : ℝ), (22698649506403/50000000000000 : ℝ), (42515073772973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984798537/10000000000 : ℝ)|^4363 ≤ (12087627190659/100000000000000 : ℝ)^3339
        have hw : |(-1984798537/10000000000 : ℝ)|=(1984798537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464184773/10000000000 : ℝ)|^4363 ≤ (22698649506403/50000000000000 : ℝ)^3339
        have hw : |(5464184773/10000000000 : ℝ)|=(5464184773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196659263/10000000000 : ℝ)|^4363 ≤ (42515073772973/100000000000000 : ℝ)^3339
        have hw : |(5196659263/10000000000 : ℝ)|=(5196659263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361816681/10000000000 : ℝ)*x 0 + (-2122602579/10000000000 : ℝ)*x 1 + (20786637/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361816681/10000000000 : ℝ)^4363 ≤ (4428918823387/10000000000000 : ℝ)^3339 := by
    have hnat : (5361816681 : ℕ)^4363*10000000000000^3339 ≤ 4428918823387^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361816681 10000000000 4428918823387 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122602579/10000000000 : ℝ)^4363 ≤ (13195738115553/100000000000000 : ℝ)^3339 := by
    have hnat : (2122602579 : ℕ)^4363*100000000000000^3339 ≤ 13195738115553^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122602579 10000000000 13195738115553 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20786637/40000000 : ℝ)^4363 ≤ (21257536817/50000000000 : ℝ)^3339 := by
    have hnat : (20786637 : ℕ)^4363*50000000000^3339 ≤ 21257536817^3339*40000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20786637 40000000 21257536817 50000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361816681/10000000000 : ℝ), (-2122602579/10000000000 : ℝ), (20786637/40000000 : ℝ)] ![(4428918823387/10000000000000 : ℝ), (13195738115553/100000000000000 : ℝ), (21257536817/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361816681/10000000000 : ℝ)|^4363 ≤ (4428918823387/10000000000000 : ℝ)^3339
        have hw : |(5361816681/10000000000 : ℝ)|=(5361816681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122602579/10000000000 : ℝ)|^4363 ≤ (13195738115553/100000000000000 : ℝ)^3339
        have hw : |(-2122602579/10000000000 : ℝ)|=(2122602579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20786637/40000000 : ℝ)|^4363 ≤ (21257536817/50000000000 : ℝ)^3339
        have hw : |(20786637/40000000 : ℝ)|=(20786637/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340454119/2500000000 : ℝ)*x 0 + (5196659481/10000000000 : ℝ)*x 1 + (-2122602547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340454119/2500000000 : ℝ)^4363 ≤ (22144593010621/50000000000000 : ℝ)^3339 := by
    have hnat : (1340454119 : ℕ)^4363*50000000000000^3339 ≤ 22144593010621^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340454119 2500000000 22144593010621 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196659481/10000000000 : ℝ)^4363 ≤ (8503015220689/20000000000000 : ℝ)^3339 := by
    have hnat : (5196659481 : ℕ)^4363*20000000000000^3339 ≤ 8503015220689^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196659481 10000000000 8503015220689 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122602547/10000000000 : ℝ)^4363 ≤ (13195737855607/100000000000000 : ℝ)^3339 := by
    have hnat : (2122602547 : ℕ)^4363*100000000000000^3339 ≤ 13195737855607^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122602547 10000000000 13195737855607 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340454119/2500000000 : ℝ), (5196659481/10000000000 : ℝ), (-2122602547/10000000000 : ℝ)] ![(22144593010621/50000000000000 : ℝ), (8503015220689/20000000000000 : ℝ), (13195737855607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340454119/2500000000 : ℝ)|^4363 ≤ (22144593010621/50000000000000 : ℝ)^3339
        have hw : |(1340454119/2500000000 : ℝ)|=(1340454119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196659481/10000000000 : ℝ)|^4363 ≤ (8503015220689/20000000000000 : ℝ)^3339
        have hw : |(5196659481/10000000000 : ℝ)|=(5196659481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122602547/10000000000 : ℝ)|^4363 ≤ (13195737855607/100000000000000 : ℝ)^3339
        have hw : |(-2122602547/10000000000 : ℝ)|=(2122602547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306074607/10000000000 : ℝ)*x 0 + (4028114201/10000000000 : ℝ)*x 1 + (2300676443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306074607/10000000000 : ℝ)^4363 ≤ (33255399948227/100000000000000 : ℝ)^3339 := by
    have hnat : (4306074607 : ℕ)^4363*100000000000000^3339 ≤ 33255399948227^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306074607 10000000000 33255399948227 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028114201/10000000000 : ℝ)^4363 ≤ (30478593492933/100000000000000 : ℝ)^3339 := by
    have hnat : (4028114201 : ℕ)^4363*100000000000000^3339 ≤ 30478593492933^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028114201 10000000000 30478593492933 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300676443/5000000000 : ℝ)^4363 ≤ (18133003270353/50000000000000 : ℝ)^3339 := by
    have hnat : (2300676443 : ℕ)^4363*50000000000000^3339 ≤ 18133003270353^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300676443 5000000000 18133003270353 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306074607/10000000000 : ℝ), (4028114201/10000000000 : ℝ), (2300676443/5000000000 : ℝ)] ![(33255399948227/100000000000000 : ℝ), (30478593492933/100000000000000 : ℝ), (18133003270353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306074607/10000000000 : ℝ)|^4363 ≤ (33255399948227/100000000000000 : ℝ)^3339
        have hw : |(4306074607/10000000000 : ℝ)|=(4306074607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028114201/10000000000 : ℝ)|^4363 ≤ (30478593492933/100000000000000 : ℝ)^3339
        have hw : |(4028114201/10000000000 : ℝ)|=(4028114201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2300676443/5000000000 : ℝ)|^4363 ≤ (18133003270353/50000000000000 : ℝ)^3339
        have hw : |(2300676443/5000000000 : ℝ)|=(2300676443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396969781/2000000000 : ℝ)*x 0 + (5198231133/10000000000 : ℝ)*x 1 + (5462599853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396969781/2000000000 : ℝ)^4363 ≤ (6044014005529/50000000000000 : ℝ)^3339 := by
    have hnat : (396969781 : ℕ)^4363*50000000000000^3339 ≤ 6044014005529^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396969781 2000000000 6044014005529 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198231133/10000000000 : ℝ)^4363 ≤ (42531878221157/100000000000000 : ℝ)^3339 := by
    have hnat : (5198231133 : ℕ)^4363*100000000000000^3339 ≤ 42531878221157^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198231133 10000000000 42531878221157 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462599853/10000000000 : ℝ)^4363 ≤ (22690046872049/50000000000000 : ℝ)^3339 := by
    have hnat : (5462599853 : ℕ)^4363*50000000000000^3339 ≤ 22690046872049^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462599853 10000000000 22690046872049 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396969781/2000000000 : ℝ), (5198231133/10000000000 : ℝ), (5462599853/10000000000 : ℝ)] ![(6044014005529/50000000000000 : ℝ), (42531878221157/100000000000000 : ℝ), (22690046872049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396969781/2000000000 : ℝ)|^4363 ≤ (6044014005529/50000000000000 : ℝ)^3339
        have hw : |(-396969781/2000000000 : ℝ)|=(396969781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198231133/10000000000 : ℝ)|^4363 ≤ (42531878221157/100000000000000 : ℝ)^3339
        have hw : |(5198231133/10000000000 : ℝ)|=(5198231133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462599853/10000000000 : ℝ)|^4363 ≤ (22690046872049/50000000000000 : ℝ)^3339
        have hw : |(5462599853/10000000000 : ℝ)|=(5462599853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292425101/10000000000 : ℝ)*x 0 + (-371332517/2000000000 : ℝ)*x 1 + (2731299781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292425101/10000000000 : ℝ)^4363 ≤ (43541714349717/100000000000000 : ℝ)^3339 := by
    have hnat : (5292425101 : ℕ)^4363*100000000000000^3339 ≤ 43541714349717^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292425101 10000000000 43541714349717 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371332517/2000000000 : ℝ)^4363 ≤ (2215639011663/20000000000000 : ℝ)^3339 := by
    have hnat : (371332517 : ℕ)^4363*20000000000000^3339 ≤ 2215639011663^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371332517 2000000000 2215639011663 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731299781/5000000000 : ℝ)^4363 ≤ (45380090585257/100000000000000 : ℝ)^3339 := by
    have hnat : (2731299781 : ℕ)^4363*100000000000000^3339 ≤ 45380090585257^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731299781 5000000000 45380090585257 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292425101/10000000000 : ℝ), (-371332517/2000000000 : ℝ), (2731299781/5000000000 : ℝ)] ![(43541714349717/100000000000000 : ℝ), (2215639011663/20000000000000 : ℝ), (45380090585257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292425101/10000000000 : ℝ)|^4363 ≤ (43541714349717/100000000000000 : ℝ)^3339
        have hw : |(5292425101/10000000000 : ℝ)|=(5292425101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-371332517/2000000000 : ℝ)|^4363 ≤ (2215639011663/20000000000000 : ℝ)^3339
        have hw : |(-371332517/2000000000 : ℝ)|=(371332517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731299781/5000000000 : ℝ)|^4363 ≤ (45380090585257/100000000000000 : ℝ)^3339
        have hw : |(2731299781/5000000000 : ℝ)|=(2731299781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646213259/5000000000 : ℝ)*x 0 + (5462599539/10000000000 : ℝ)*x 1 + (-928330331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646213259/5000000000 : ℝ)^4363 ≤ (21770864791429/50000000000000 : ℝ)^3339 := by
    have hnat : (2646213259 : ℕ)^4363*50000000000000^3339 ≤ 21770864791429^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646213259 5000000000 21770864791429 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462599539/10000000000 : ℝ)^4363 ≤ (45380090335589/100000000000000 : ℝ)^3339 := by
    have hnat : (5462599539 : ℕ)^4363*100000000000000^3339 ≤ 45380090335589^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462599539 10000000000 45380090335589 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928330331/5000000000 : ℝ)^4363 ≤ (11078180065471/100000000000000 : ℝ)^3339 := by
    have hnat : (928330331 : ℕ)^4363*100000000000000^3339 ≤ 11078180065471^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928330331 5000000000 11078180065471 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646213259/5000000000 : ℝ), (5462599539/10000000000 : ℝ), (-928330331/5000000000 : ℝ)] ![(21770864791429/50000000000000 : ℝ), (45380090335589/100000000000000 : ℝ), (11078180065471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646213259/5000000000 : ℝ)|^4363 ≤ (21770864791429/50000000000000 : ℝ)^3339
        have hw : |(2646213259/5000000000 : ℝ)|=(2646213259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462599539/10000000000 : ℝ)|^4363 ≤ (45380090335589/100000000000000 : ℝ)^3339
        have hw : |(5462599539/10000000000 : ℝ)|=(5462599539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-928330331/5000000000 : ℝ)|^4363 ≤ (11078180065471/100000000000000 : ℝ)^3339
        have hw : |(-928330331/5000000000 : ℝ)|=(928330331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s2_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861236759/2000000000 : ℝ)*x 0 + (4597985267/10000000000 : ℝ)*x 1 + (4031509797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861236759/2000000000 : ℝ)^4363 ≤ (6651300361443/20000000000000 : ℝ)^3339 := by
    have hnat : (861236759 : ℕ)^4363*20000000000000^3339 ≤ 6651300361443^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861236759 2000000000 6651300361443 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4597985267/10000000000 : ℝ)^4363 ≤ (283057252261/781250000000 : ℝ)^3339 := by
    have hnat : (4597985267 : ℕ)^4363*781250000000^3339 ≤ 283057252261^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597985267 10000000000 283057252261 781250000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031509797/10000000000 : ℝ)^4363 ≤ (1220486795553/4000000000000 : ℝ)^3339 := by
    have hnat : (4031509797 : ℕ)^4363*4000000000000^3339 ≤ 1220486795553^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031509797 10000000000 1220486795553 4000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861236759/2000000000 : ℝ), (4597985267/10000000000 : ℝ), (4031509797/10000000000 : ℝ)] ![(6651300361443/20000000000000 : ℝ), (283057252261/781250000000 : ℝ), (1220486795553/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861236759/2000000000 : ℝ)|^4363 ≤ (6651300361443/20000000000000 : ℝ)^3339
        have hw : |(861236759/2000000000 : ℝ)|=(861236759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4597985267/10000000000 : ℝ)|^4363 ≤ (283057252261/781250000000 : ℝ)^3339
        have hw : |(4597985267/10000000000 : ℝ)|=(4597985267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031509797/10000000000 : ℝ)|^4363 ≤ (1220486795553/4000000000000 : ℝ)^3339
        have hw : |(4031509797/10000000000 : ℝ)|=(4031509797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (639/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15883/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7433/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (1553902540226601/100000000000000000000 : ℝ) := by
    have hpowers : (7433/100000 : ℝ)^2181 ≤ (1553902540226601/100000000000000000000 : ℝ)^512 := by
      have hnat : (7433 : ℕ)^2181*100000000000000000000^512 ≤ 1553902540226601^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7433 100000 1553902540226601 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7433/100000 : ℝ)) (X := (1553902540226601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19023/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (85093716621334943/100000000000000000000 : ℝ) := by
    have hpowers : (19023/100000 : ℝ)^2181 ≤ (85093716621334943/100000000000000000000 : ℝ)^512 := by
      have hnat : (19023 : ℕ)^2181*100000000000000000000^512 ≤ 85093716621334943^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19023 100000 85093716621334943 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19023/100000 : ℝ)) (X := (85093716621334943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001553902540226601/50000000000000000000 : ℝ) ≤ (10000072956317303/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50001553902540226601/50000000000000000000 : ℝ)^512 ≤ (10000072956317303/10000000000000000 : ℝ)^2181 := by
      have hnat : (50001553902540226601 : ℕ)^512*10000000000000000^2181 ≤ 10000072956317303^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001553902540226601 50000000000000000000 10000072956317303 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000072956317303/10000000000000000 : ℝ)) (X := (50001553902540226601/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12510830952395195193/12500000000000000000 : ℝ) ≤ (10002033419555043/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (12510830952395195193/12500000000000000000 : ℝ)^512 ≤ (10002033419555043/10000000000000000 : ℝ)^2181 := by
      have hnat : (12510830952395195193 : ℕ)^512*10000000000000000^2181 ≤ 10002033419555043^2181*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510830952395195193 12500000000000000000 10002033419555043 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002033419555043/10000000000000000 : ℝ)) (X := (12510830952395195193/12500000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50085093716621334943/50000000000000000000 : ℝ) ≤ (10003993882792783/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50085093716621334943/50000000000000000000 : ℝ)^512 ≤ (10003993882792783/10000000000000000 : ℝ)^2181 := by
      have hnat : (50085093716621334943 : ℕ)^512*10000000000000000^2181 ≤ 10003993882792783^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50085093716621334943 50000000000000000000 10003993882792783 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003993882792783/10000000000000000 : ℝ)) (X := (50085093716621334943/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1553902540226601/100000000000000000000 : ℝ) ≤ ((11587170131722529893/11590000000000000000 : ℝ)+2*(98023161887/57950000000000 : ℝ)*(7433/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (11587170131722529893/11590000000000000000 : ℝ)+2*(98023161887/57950000000000 : ℝ)*(7433/100000 : ℝ)=(10000072956317303/10000000000000000 : ℝ) by norm_num, show 1+2*(1553902540226601/100000000000000000000 : ℝ)=(50001553902540226601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85093716621334943/100000000000000000000 : ℝ)+(1553902540226601/100000000000000000000 : ℝ) ≤ ((11587170131722529893/11590000000000000000 : ℝ)+(98023161887/57950000000000 : ℝ)*((19023/100000 : ℝ)+(7433/100000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (11587170131722529893/11590000000000000000 : ℝ)+(98023161887/57950000000000 : ℝ)*((19023/100000 : ℝ)+(7433/100000 : ℝ))=(10002033419555043/10000000000000000 : ℝ) by norm_num, show 1+(85093716621334943/100000000000000000000 : ℝ)+(1553902540226601/100000000000000000000 : ℝ)=(12510830952395195193/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85093716621334943/100000000000000000000 : ℝ) ≤ ((11587170131722529893/11590000000000000000 : ℝ)+2*(98023161887/57950000000000 : ℝ)*(19023/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (11587170131722529893/11590000000000000000 : ℝ)+2*(98023161887/57950000000000 : ℝ)*(19023/100000 : ℝ)=(10003993882792783/10000000000000000 : ℝ) by norm_num, show 1+2*(85093716621334943/100000000000000000000 : ℝ)=(50085093716621334943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11587170131722529893/11590000000000000000 : ℝ)*(X 1 0+X 2 0)+(98023161887/57950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (19023/100000 : ℝ)) (c := (11587170131722529893/11590000000000000000 : ℝ)) (alpha := (98023161887/57950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11587170131722529893/11590000000000000000 : ℝ)*(X 0 1+X 2 1)+(98023161887/57950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (19023/100000 : ℝ)) (c := (11587170131722529893/11590000000000000000 : ℝ)) (alpha := (98023161887/57950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11587170131722529893/11590000000000000000 : ℝ)*(X 0 2+X 1 2)+(98023161887/57950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (7433/100000 : ℝ)) (hi := (19023/100000 : ℝ)) (c := (11587170131722529893/11590000000000000000 : ℝ)) (alpha := (98023161887/57950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984798537/10000000000 : ℝ)*X 0 0+(5464184773/10000000000 : ℝ)*X 0 1+(5196659263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361816681/10000000000 : ℝ)*X 1 0+(-2122602579/10000000000 : ℝ)*X 1 1+(20786637/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340454119/2500000000 : ℝ)*X 2 0+(5196659481/10000000000 : ℝ)*X 2 1+(-2122602547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306074607/10000000000 : ℝ)*X 0 0+(4028114201/10000000000 : ℝ)*X 0 1+(2300676443/5000000000 : ℝ)*X 0 2+(4306074607/10000000000 : ℝ)*X 1 0+(4028114201/10000000000 : ℝ)*X 1 1+(2300676443/5000000000 : ℝ)*X 1 2+(4306074607/10000000000 : ℝ)*X 2 0+(4028114201/10000000000 : ℝ)*X 2 1+(2300676443/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-396969781/2000000000 : ℝ)*X 0 0+(5198231133/10000000000 : ℝ)*X 0 1+(5462599853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292425101/10000000000 : ℝ)*X 1 0+(-371332517/2000000000 : ℝ)*X 1 1+(2731299781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646213259/5000000000 : ℝ)*X 2 0+(5462599539/10000000000 : ℝ)*X 2 1+(-928330331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861236759/2000000000 : ℝ)*X 0 0+(4597985267/10000000000 : ℝ)*X 0 1+(4031509797/10000000000 : ℝ)*X 0 2+(861236759/2000000000 : ℝ)*X 1 0+(4597985267/10000000000 : ℝ)*X 1 1+(4031509797/10000000000 : ℝ)*X 1 2+(861236759/2000000000 : ℝ)*X 2 0+(4597985267/10000000000 : ℝ)*X 2 1+(4031509797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10466583049953646089393/1448750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1162123141/100000000000000 : ℝ)*(base19) + (171897007/20000000000000 : ℝ)*(base23) + (85640247/100000000000000 : ℝ)*(lower2) + (108840717/50000000000000 : ℝ)*(upper3) + (44050277/50000000000000 : ℝ)*(upper5) + (685309579472273/25000000000000 : ℝ)*(major0) + (685309579472273/25000000000000 : ℝ)*(major1) + (685309579472273/25000000000000 : ℝ)*(major2) + (1868988199359813/50000000000000 : ℝ)*(sp0) + (934496964614449/25000000000000 : ℝ)*(sp1) + (1868994080547951/50000000000000 : ℝ)*(sp2) + (1744479985217129/100000000000000 : ℝ)*(sp3) + (12621861311/100000000000000 : ℝ)*(sp4) + (1477832281/20000000000000 : ℝ)*(sp7) + (872243687189267/50000000000000 : ℝ)*(f.failure) + (1868994510290469/50000000000000 : ℝ)*(f.sum) + (19920569492287/5795000000000000000000000000 : ℝ)*base66 + (1545097286818606789/289750000000000000000000000000000 : ℝ)*base67 + (369290430762643211/289750000000000000000000000000000 : ℝ)*base70 + (149056773834143211/289750000000000000000000000000000 : ℝ)*base72 + (1293855251223/1448750000000000000000000000 : ℝ)*base74 + (73960403847106789/289750000000000000000000000000000 : ℝ)*base75 + (737940697305143211/289750000000000000000000000000000 : ℝ)*base78 + (344171446678856789/289750000000000000000000000000000 : ℝ)*base79 + (25573783366367/5795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4214861/5000000000000000000000 : ℝ)*base89 + (4214861/5000000000000000000000 : ℝ)*base91 + (4214861/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150915979413265036190562429/18109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139999683/12500000000000 : ℝ)*(base19) + (1634730163/50000000000000 : ℝ)*(base23) + (47546697/20000000000000 : ℝ)*(upper3) + (316245371/100000000000000 : ℝ)*(lower4) + (46209573/50000000000000 : ℝ)*(upper5) + (173371874961499/6250000000000 : ℝ)*(major0) + (173371874961499/6250000000000 : ℝ)*(major1) + (173371874961499/6250000000000 : ℝ)*(major2) + (6030702749/100000000000000 : ℝ)*(sp1) + (4715329127/10000000000000 : ℝ)*(sp2) + (945648767585417/25000000000000 : ℝ)*(sp4) + (236411744977591/6250000000000 : ℝ)*(sp5) + (472818080948759/12500000000000 : ℝ)*(sp6) + (441326162660047/25000000000000 : ℝ)*(sp7) + (441326162660047/25000000000000 : ℝ)*(f.failure) + (945648767585417/25000000000000 : ℝ)*(f.sum) + (175496943799/362187500000000000000000000 : ℝ)*base66 + (458899955076689607/72437500000000000000000000000000 : ℝ)*base67 + (1054507403864189607/72437500000000000000000000000000 : ℝ)*base69 + (465789110901747893/72437500000000000000000000000000 : ℝ)*base72 + (31228883782441/5795000000000000000000000000 : ℝ)*base73 + (833040923416564607/72437500000000000000000000000000 : ℝ)*base75 + (217734710918939607/72437500000000000000000000000000 : ℝ)*base77 + (471688228226314607/72437500000000000000000000000000 : ℝ)*base79 + (12824981793713/2897500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (27772399/2500000000000000000000 : ℝ)*base90 + (27772399/2500000000000000000000 : ℝ)*base92 + (27772399/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1403_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1403_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1403_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1403_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1403_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (639/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15883/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
