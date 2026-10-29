-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:08.391987+00:00
-- url     : https://prove2.me/submissions/167d2332-2801-4610-8969-74f43acc6fa1

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
theorem support_rectangle_w1422_s6_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976823331/10000000000 : ℝ)*x 0 + (5408581063/10000000000 : ℝ)*x 1 + (163960853/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976823331/10000000000 : ℝ)^2191 ≤ (12058072474731/100000000000000 : ℝ)^1679 := by
    have hnat : (1976823331 : ℕ)^2191*100000000000000^1679 ≤ 12058072474731^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976823331 10000000000 12058072474731 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408581063/10000000000 : ℝ)^2191 ≤ (44842401764361/100000000000000 : ℝ)^1679 := by
    have hnat : (5408581063 : ℕ)^2191*100000000000000^1679 ≤ 44842401764361^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408581063 10000000000 44842401764361 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163960853/312500000 : ℝ)^2191 ≤ (5387440717683/12500000000000 : ℝ)^1679 := by
    have hnat : (163960853 : ℕ)^2191*12500000000000^1679 ≤ 5387440717683^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163960853 312500000 5387440717683 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976823331/10000000000 : ℝ), (5408581063/10000000000 : ℝ), (163960853/312500000 : ℝ)] ![(12058072474731/100000000000000 : ℝ), (44842401764361/100000000000000 : ℝ), (5387440717683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976823331/10000000000 : ℝ)|^2191 ≤ (12058072474731/100000000000000 : ℝ)^1679
        have hw : |(-1976823331/10000000000 : ℝ)|=(1976823331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408581063/10000000000 : ℝ)|^2191 ≤ (44842401764361/100000000000000 : ℝ)^1679
        have hw : |(5408581063/10000000000 : ℝ)|=(5408581063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163960853/312500000 : ℝ)|^2191 ≤ (5387440717683/12500000000000 : ℝ)^1679
        have hw : |(163960853/312500000 : ℝ)|=(163960853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336868429/2500000000 : ℝ)*x 0 + (-514805153/2500000000 : ℝ)*x 1 + (2623373647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336868429/2500000000 : ℝ)^2191 ≤ (2761400495951/6250000000000 : ℝ)^1679 := by
    have hnat : (1336868429 : ℕ)^2191*6250000000000^1679 ≤ 2761400495951^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336868429 2500000000 2761400495951 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514805153/2500000000 : ℝ)^2191 ≤ (1589758291243/12500000000000 : ℝ)^1679 := by
    have hnat : (514805153 : ℕ)^2191*12500000000000^1679 ≤ 1589758291243^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514805153 2500000000 1589758291243 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623373647/5000000000 : ℝ)^2191 ≤ (1723981028801/4000000000000 : ℝ)^1679 := by
    have hnat : (2623373647 : ℕ)^2191*4000000000000^1679 ≤ 1723981028801^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623373647 5000000000 1723981028801 4000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336868429/2500000000 : ℝ), (-514805153/2500000000 : ℝ), (2623373647/5000000000 : ℝ)] ![(2761400495951/6250000000000 : ℝ), (1589758291243/12500000000000 : ℝ), (1723981028801/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336868429/2500000000 : ℝ)|^2191 ≤ (2761400495951/6250000000000 : ℝ)^1679
        have hw : |(1336868429/2500000000 : ℝ)|=(1336868429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514805153/2500000000 : ℝ)|^2191 ≤ (1589758291243/12500000000000 : ℝ)^1679
        have hw : |(-514805153/2500000000 : ℝ)|=(514805153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623373647/5000000000 : ℝ)|^2191 ≤ (1723981028801/4000000000000 : ℝ)^1679
        have hw : |(2623373647/5000000000 : ℝ)|=(2623373647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347473939/10000000000 : ℝ)*x 0 + (5246747061/10000000000 : ℝ)*x 1 + (-128701289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347473939/10000000000 : ℝ)^2191 ≤ (44182410339563/100000000000000 : ℝ)^1679 := by
    have hnat : (5347473939 : ℕ)^2191*100000000000000^1679 ≤ 44182410339563^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347473939 10000000000 44182410339563 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246747061/10000000000 : ℝ)^2191 ≤ (8619904644477/20000000000000 : ℝ)^1679 := by
    have hnat : (5246747061 : ℕ)^2191*20000000000000^1679 ≤ 8619904644477^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246747061 10000000000 8619904644477 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128701289/625000000 : ℝ)^2191 ≤ (6359033213329/50000000000000 : ℝ)^1679 := by
    have hnat : (128701289 : ℕ)^2191*50000000000000^1679 ≤ 6359033213329^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128701289 625000000 6359033213329 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347473939/10000000000 : ℝ), (5246747061/10000000000 : ℝ), (-128701289/625000000 : ℝ)] ![(44182410339563/100000000000000 : ℝ), (8619904644477/20000000000000 : ℝ), (6359033213329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347473939/10000000000 : ℝ)|^2191 ≤ (44182410339563/100000000000000 : ℝ)^1679
        have hw : |(5347473939/10000000000 : ℝ)|=(5347473939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246747061/10000000000 : ℝ)|^2191 ≤ (8619904644477/20000000000000 : ℝ)^1679
        have hw : |(5246747061/10000000000 : ℝ)|=(5246747061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128701289/625000000 : ℝ)|^2191 ≤ (6359033213329/50000000000000 : ℝ)^1679
        have hw : |(-128701289/625000000 : ℝ)|=(128701289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4306126369/10000000000 : ℝ)*x 0 + (4134718943/10000000000 : ℝ)*x 1 + (4483922189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306126369/10000000000 : ℝ)^2191 ≤ (1665228916857/5000000000000 : ℝ)^1679 := by
    have hnat : (4306126369 : ℕ)^2191*5000000000000^1679 ≤ 1665228916857^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306126369 10000000000 1665228916857 5000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134718943/10000000000 : ℝ)^2191 ≤ (1579260336871/5000000000000 : ℝ)^1679 := by
    have hnat : (4134718943 : ℕ)^2191*5000000000000^1679 ≤ 1579260336871^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134718943 10000000000 1579260336871 5000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483922189/10000000000 : ℝ)^2191 ≤ (7022042981551/20000000000000 : ℝ)^1679 := by
    have hnat : (4483922189 : ℕ)^2191*20000000000000^1679 ≤ 7022042981551^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483922189 10000000000 7022042981551 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306126369/10000000000 : ℝ), (4134718943/10000000000 : ℝ), (4483922189/10000000000 : ℝ)] ![(1665228916857/5000000000000 : ℝ), (1579260336871/5000000000000 : ℝ), (7022042981551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306126369/10000000000 : ℝ)|^2191 ≤ (1665228916857/5000000000000 : ℝ)^1679
        have hw : |(4306126369/10000000000 : ℝ)|=(4306126369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134718943/10000000000 : ℝ)|^2191 ≤ (1579260336871/5000000000000 : ℝ)^1679
        have hw : |(4134718943/10000000000 : ℝ)|=(4134718943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483922189/10000000000 : ℝ)|^2191 ≤ (7022042981551/20000000000000 : ℝ)^1679
        have hw : |(4483922189/10000000000 : ℝ)|=(4483922189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976834867/10000000000 : ℝ)*x 0 + (1049466133/2000000000 : ℝ)*x 1 + (5407994567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976834867/10000000000 : ℝ)^2191 ≤ (3014541074743/25000000000000 : ℝ)^1679 := by
    have hnat : (1976834867 : ℕ)^2191*25000000000000^1679 ≤ 3014541074743^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976834867 10000000000 3014541074743 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049466133/2000000000 : ℝ)^2191 ≤ (1347055602007/3125000000000 : ℝ)^1679 := by
    have hnat : (1049466133 : ℕ)^2191*3125000000000^1679 ≤ 1347055602007^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049466133 2000000000 1347055602007 3125000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407994567/10000000000 : ℝ)^2191 ≤ (5604507052717/12500000000000 : ℝ)^1679 := by
    have hnat : (5407994567 : ℕ)^2191*12500000000000^1679 ≤ 5604507052717^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407994567 10000000000 5604507052717 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976834867/10000000000 : ℝ), (1049466133/2000000000 : ℝ), (5407994567/10000000000 : ℝ)] ![(3014541074743/25000000000000 : ℝ), (1347055602007/3125000000000 : ℝ), (5604507052717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976834867/10000000000 : ℝ)|^2191 ≤ (3014541074743/25000000000000 : ℝ)^1679
        have hw : |(-1976834867/10000000000 : ℝ)|=(1976834867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049466133/2000000000 : ℝ)|^2191 ≤ (1347055602007/3125000000000 : ℝ)^1679
        have hw : |(1049466133/2000000000 : ℝ)|=(1049466133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407994567/10000000000 : ℝ)|^2191 ≤ (5604507052717/12500000000000 : ℝ)^1679
        have hw : |(5407994567/10000000000 : ℝ)|=(5407994567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652715137/5000000000 : ℝ)*x 0 + (-948986609/5000000000 : ℝ)*x 1 + (5407994703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652715137/5000000000 : ℝ)^2191 ≤ (43729647175771/100000000000000 : ℝ)^1679 := by
    have hnat : (2652715137 : ℕ)^2191*100000000000000^1679 ≤ 43729647175771^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652715137 5000000000 43729647175771 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948986609/5000000000 : ℝ)^2191 ≤ (2286858983581/20000000000000 : ℝ)^1679 := by
    have hnat : (948986609 : ℕ)^2191*20000000000000^1679 ≤ 2286858983581^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948986609 5000000000 2286858983581 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407994703/10000000000 : ℝ)^2191 ≤ (22418028946553/50000000000000 : ℝ)^1679 := by
    have hnat : (5407994703 : ℕ)^2191*50000000000000^1679 ≤ 22418028946553^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407994703 10000000000 22418028946553 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652715137/5000000000 : ℝ), (-948986609/5000000000 : ℝ), (5407994703/10000000000 : ℝ)] ![(43729647175771/100000000000000 : ℝ), (2286858983581/20000000000000 : ℝ), (22418028946553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652715137/5000000000 : ℝ)|^2191 ≤ (43729647175771/100000000000000 : ℝ)^1679
        have hw : |(2652715137/5000000000 : ℝ)|=(2652715137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948986609/5000000000 : ℝ)|^2191 ≤ (2286858983581/20000000000000 : ℝ)^1679
        have hw : |(-948986609/5000000000 : ℝ)|=(948986609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407994703/10000000000 : ℝ)|^2191 ≤ (22418028946553/50000000000000 : ℝ)^1679
        have hw : |(5407994703/10000000000 : ℝ)|=(5407994703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305429973/10000000000 : ℝ)*x 0 + (1351998777/2500000000 : ℝ)*x 1 + (-1897973073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305429973/10000000000 : ℝ)^2191 ≤ (43729643938243/100000000000000 : ℝ)^1679 := by
    have hnat : (5305429973 : ℕ)^2191*100000000000000^1679 ≤ 43729643938243^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305429973 10000000000 43729643938243 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351998777/2500000000 : ℝ)^2191 ≤ (22418031137379/50000000000000 : ℝ)^1679 := by
    have hnat : (1351998777 : ℕ)^2191*50000000000000^1679 ≤ 22418031137379^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351998777 2500000000 22418031137379 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897973073/10000000000 : ℝ)^2191 ≤ (11434293777973/100000000000000 : ℝ)^1679 := by
    have hnat : (1897973073 : ℕ)^2191*100000000000000^1679 ≤ 11434293777973^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897973073 10000000000 11434293777973 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305429973/10000000000 : ℝ), (1351998777/2500000000 : ℝ), (-1897973073/10000000000 : ℝ)] ![(43729643938243/100000000000000 : ℝ), (22418031137379/50000000000000 : ℝ), (11434293777973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305429973/10000000000 : ℝ)|^2191 ≤ (43729643938243/100000000000000 : ℝ)^1679
        have hw : |(5305429973/10000000000 : ℝ)|=(5305429973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351998777/2500000000 : ℝ)|^2191 ≤ (22418031137379/50000000000000 : ℝ)^1679
        have hw : |(1351998777/2500000000 : ℝ)|=(1351998777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1897973073/10000000000 : ℝ)|^2191 ≤ (11434293777973/100000000000000 : ℝ)^1679
        have hw : |(-1897973073/10000000000 : ℝ)|=(1897973073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s6_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134567223/312500000 : ℝ)*x 0 + (280166463/625000000 : ℝ)*x 1 + (827196809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134567223/312500000 : ℝ)^2191 ≤ (6660965660823/20000000000000 : ℝ)^1679 := by
    have hnat : (134567223 : ℕ)^2191*20000000000000^1679 ≤ 6660965660823^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134567223 312500000 6660965660823 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280166463/625000000 : ℝ)^2191 ≤ (35097353198447/100000000000000 : ℝ)^1679 := by
    have hnat : (280166463 : ℕ)^2191*100000000000000^1679 ≤ 35097353198447^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280166463 625000000 35097353198447 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827196809/2000000000 : ℝ)^2191 ≤ (6319563696667/20000000000000 : ℝ)^1679 := by
    have hnat : (827196809 : ℕ)^2191*20000000000000^1679 ≤ 6319563696667^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827196809 2000000000 6319563696667 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134567223/312500000 : ℝ), (280166463/625000000 : ℝ), (827196809/2000000000 : ℝ)] ![(6660965660823/20000000000000 : ℝ), (35097353198447/100000000000000 : ℝ), (6319563696667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134567223/312500000 : ℝ)|^2191 ≤ (6660965660823/20000000000000 : ℝ)^1679
        have hw : |(134567223/312500000 : ℝ)|=(134567223/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280166463/625000000 : ℝ)|^2191 ≤ (35097353198447/100000000000000 : ℝ)^1679
        have hw : |(280166463/625000000 : ℝ)|=(280166463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827196809/2000000000 : ℝ)|^2191 ≤ (6319563696667/20000000000000 : ℝ)^1679
        have hw : |(827196809/2000000000 : ℝ)|=(827196809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5663/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5661/50000 : ℝ) ^ (4381/1024 : ℝ) ≤ (560093090569093/6250000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^4381 ≤ (560093090569093/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5661 : ℕ)^4381*6250000000000000000^1024 ≤ 560093090569093^1024*50000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 560093090569093 6250000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (560093090569093/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (4381/1024 : ℝ) ≤ (6960614838027531/25000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^4381 ≤ (6960614838027531/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14757 : ℕ)^4381*25000000000000000000^1024 ≤ 6960614838027531^1024*100000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 6960614838027531 25000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (6960614838027531/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125560093090569093/3125000000000000000 : ℝ) ≤ (10000418896832703/10000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (3125560093090569093/3125000000000000000 : ℝ)^1024 ≤ (10000418896832703/10000000000000000 : ℝ)^4381 := by
      have hnat : (3125560093090569093 : ℕ)^1024*10000000000000000^4381 ≤ 10000418896832703^4381*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125560093090569093 3125000000000000000 10000418896832703 10000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000418896832703/10000000000000000 : ℝ)) (X := (3125560093090569093/3125000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009200987200303903/25000000000000000000 : ℝ) ≤ (10000860121673957/10000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (25009200987200303903/25000000000000000000 : ℝ)^1024 ≤ (10000860121673957/10000000000000000 : ℝ)^4381 := by
      have hnat : (25009200987200303903 : ℕ)^1024*10000000000000000^4381 ≤ 10000860121673957^4381*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009200987200303903 25000000000000000000 10000860121673957 10000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000860121673957/10000000000000000 : ℝ)) (X := (25009200987200303903/25000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506960614838027531/12500000000000000000 : ℝ) ≤ (10001301346515211/10000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (12506960614838027531/12500000000000000000 : ℝ)^1024 ≤ (10001301346515211/10000000000000000 : ℝ)^4381 := by
      have hnat : (12506960614838027531 : ℕ)^1024*10000000000000000^4381 ≤ 10001301346515211^4381*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506960614838027531 12500000000000000000 10001301346515211 10000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001301346515211/10000000000000000 : ℝ)) (X := (12506960614838027531/12500000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(560093090569093/6250000000000000000 : ℝ) ≤ ((11447149271771659743/11450000000000000000 : ℝ)+2*(220612420627/171750000000000 : ℝ)*(5661/50000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (11447149271771659743/11450000000000000000 : ℝ)+2*(220612420627/171750000000000 : ℝ)*(5661/50000 : ℝ)=(10000418896832703/10000000000000000 : ℝ) by norm_num, show 1+2*(560093090569093/6250000000000000000 : ℝ)=(3125560093090569093/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6960614838027531/25000000000000000000 : ℝ)+(560093090569093/6250000000000000000 : ℝ) ≤ ((11447149271771659743/11450000000000000000 : ℝ)+(220612420627/171750000000000 : ℝ)*((14757/100000 : ℝ)+(5661/50000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (11447149271771659743/11450000000000000000 : ℝ)+(220612420627/171750000000000 : ℝ)*((14757/100000 : ℝ)+(5661/50000 : ℝ))=(10000860121673957/10000000000000000 : ℝ) by norm_num, show 1+(6960614838027531/25000000000000000000 : ℝ)+(560093090569093/6250000000000000000 : ℝ)=(25009200987200303903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6960614838027531/25000000000000000000 : ℝ) ≤ ((11447149271771659743/11450000000000000000 : ℝ)+2*(220612420627/171750000000000 : ℝ)*(14757/100000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (11447149271771659743/11450000000000000000 : ℝ)+2*(220612420627/171750000000000 : ℝ)*(14757/100000 : ℝ)=(10001301346515211/10000000000000000 : ℝ) by norm_num, show 1+2*(6960614838027531/25000000000000000000 : ℝ)=(12506960614838027531/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11447149271771659743/11450000000000000000 : ℝ)*(X 1 0+X 2 0)+(220612420627/171750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (11447149271771659743/11450000000000000000 : ℝ)) (alpha := (220612420627/171750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11447149271771659743/11450000000000000000 : ℝ)*(X 0 1+X 2 1)+(220612420627/171750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (11447149271771659743/11450000000000000000 : ℝ)) (alpha := (220612420627/171750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11447149271771659743/11450000000000000000 : ℝ)*(X 0 2+X 1 2)+(220612420627/171750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (11447149271771659743/11450000000000000000 : ℝ)) (alpha := (220612420627/171750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1976823331/10000000000 : ℝ)*X 0 0+(5408581063/10000000000 : ℝ)*X 0 1+(163960853/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336868429/2500000000 : ℝ)*X 1 0+(-514805153/2500000000 : ℝ)*X 1 1+(2623373647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347473939/10000000000 : ℝ)*X 2 0+(5246747061/10000000000 : ℝ)*X 2 1+(-128701289/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306126369/10000000000 : ℝ)*X 0 0+(4134718943/10000000000 : ℝ)*X 0 1+(4483922189/10000000000 : ℝ)*X 0 2+(4306126369/10000000000 : ℝ)*X 1 0+(4134718943/10000000000 : ℝ)*X 1 1+(4483922189/10000000000 : ℝ)*X 1 2+(4306126369/10000000000 : ℝ)*X 2 0+(4134718943/10000000000 : ℝ)*X 2 1+(4483922189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1976834867/10000000000 : ℝ)*X 0 0+(1049466133/2000000000 : ℝ)*X 0 1+(5407994567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652715137/5000000000 : ℝ)*X 1 0+(-948986609/5000000000 : ℝ)*X 1 1+(5407994703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305429973/10000000000 : ℝ)*X 2 0+(1351998777/2500000000 : ℝ)*X 2 1+(-1897973073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134567223/312500000 : ℝ)*X 0 0+(280166463/625000000 : ℝ)*X 0 1+(827196809/2000000000 : ℝ)*X 0 2+(134567223/312500000 : ℝ)*X 1 0+(280166463/625000000 : ℝ)*X 1 1+(827196809/2000000000 : ℝ)*X 1 2+(134567223/312500000 : ℝ)*X 2 0+(280166463/625000000 : ℝ)*X 2 1+(827196809/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1089587922833916312486869783/286250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13735091/20000000000000 : ℝ)*(base23) + (22576793/25000000000000 : ℝ)*(lower2) + (247167/20000000000000 : ℝ)*(lower3) + (2148721/25000000000000 : ℝ)*(upper4) + (43734641/50000000000000 : ℝ)*(lower5) + (4521421882058573/100000000000000 : ℝ)*(major0) + (4521421882058573/100000000000000 : ℝ)*(major1) + (4521421882058573/100000000000000 : ℝ)*(major2) + (6179179109308711/100000000000000 : ℝ)*(sp0) + (6179179109308711/100000000000000 : ℝ)*(sp1) + (3089589262299217/50000000000000 : ℝ)*(sp2) + (1431830854660789/50000000000000 : ℝ)*(sp3) + (516034823/100000000000000 : ℝ)*(sp6) + (563721231/20000000000000 : ℝ)*(sp7) + (1431832263963867/50000000000000 : ℝ)*(f.failure) + (6179179109308711/100000000000000 : ℝ)*(f.sum) + (449857473109867/17175000000000000000000000000 : ℝ)*base65 + (51889677131465580217/3435000000000000000000000000000000 : ℝ)*base67 + (11008647788555580217/3435000000000000000000000000000000 : ℝ)*base69 + (104306388185780580217/3435000000000000000000000000000000 : ℝ)*base71 + (2936052751649/2146875000000000000000000000 : ℝ)*base73 + (39239598633125580217/3435000000000000000000000000000000 : ℝ)*base75 + (195587264165580217/3435000000000000000000000000000000 : ℝ)*base77 + (5821100289309419783/3435000000000000000000000000000000 : ℝ)*base80 + (1864139189399/2146875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1339379/500000000000000000000 : ℝ)*base89 + (1339379/500000000000000000000 : ℝ)*base91 + (1339379/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2203784175846092875599121871/572500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18844523/25000000000000 : ℝ)*(base21) + (5009863/10000000000000 : ℝ)*(base29) + (14951413/50000000000000 : ℝ)*(upper2) + (11523943/20000000000000 : ℝ)*(upper3) + (15234753/20000000000000 : ℝ)*(lower4) + (4554340837244101/100000000000000 : ℝ)*(major0) + (455434088734273/10000000000000 : ℝ)*(major1) + (455434088734273/10000000000000 : ℝ)*(major2) + (10913357081/100000000000000 : ℝ)*(sp2) + (18316309/800000000000 : ℝ)*(sp3) + (6224167706426073/100000000000000 : ℝ)*(sp4) + (1244833531265489/20000000000000 : ℝ)*(sp5) + (622415666759227/10000000000000 : ℝ)*(sp6) + (360563956300907/12500000000000 : ℝ)*(sp7) + (2884513939945881/100000000000000 : ℝ)*(f.failure) + (6224167706426073/100000000000000 : ℝ)*(f.sum) + (2683838225717/1717500000000000000000000000 : ℝ)*base65 + (312681502321615517/343500000000000000000000000000000 : ℝ)*base67 + (14966001400363615517/343500000000000000000000000000000 : ℝ)*base69 + (23204402975374778129/3435000000000000000000000000000000 : ℝ)*base71 + (14938689112381/8587500000000000000000000000 : ℝ)*base73 + (5227161275558044483/343500000000000000000000000000000 : ℝ)*base76 + (90909452343409778129/3435000000000000000000000000000000 : ℝ)*base77 + (11309502531572044483/343500000000000000000000000000000 : ℝ)*base80 + (9128157138097/4293750000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (11481503/1000000000000000000000 : ℝ)*base90 + (1481503/1000000000000000000000 : ℝ)*base92 + (1481503/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1422_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1422_box_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-907828163/5000000000 : ℝ)*x 0 + (5386556789/10000000000 : ℝ)*x 1 + (5386556507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907828163/5000000000 : ℝ)^2191 ≤ (10791475630747/100000000000000 : ℝ)^1679 := by
    have hnat : (907828163 : ℕ)^2191*100000000000000^1679 ≤ 10791475630747^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907828163 5000000000 10791475630747 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386556789/10000000000 : ℝ)^2191 ≤ (44604263698723/100000000000000 : ℝ)^1679 := by
    have hnat : (5386556789 : ℕ)^2191*100000000000000^1679 ≤ 44604263698723^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386556789 10000000000 44604263698723 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386556507/10000000000 : ℝ)^2191 ≤ (44604260651489/100000000000000 : ℝ)^1679 := by
    have hnat : (5386556507 : ℕ)^2191*100000000000000^1679 ≤ 44604260651489^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386556507 10000000000 44604260651489 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907828163/5000000000 : ℝ), (5386556789/10000000000 : ℝ), (5386556507/10000000000 : ℝ)] ![(10791475630747/100000000000000 : ℝ), (44604263698723/100000000000000 : ℝ), (44604260651489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907828163/5000000000 : ℝ)|^2191 ≤ (10791475630747/100000000000000 : ℝ)^1679
        have hw : |(-907828163/5000000000 : ℝ)|=(907828163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386556789/10000000000 : ℝ)|^2191 ≤ (44604263698723/100000000000000 : ℝ)^1679
        have hw : |(5386556789/10000000000 : ℝ)|=(5386556789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386556507/10000000000 : ℝ)|^2191 ≤ (44604260651489/100000000000000 : ℝ)^1679
        have hw : |(5386556507/10000000000 : ℝ)|=(5386556507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286012797/10000000000 : ℝ)*x 0 + (-195376081/1000000000 : ℝ)*x 1 + (1077311321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286012797/10000000000 : ℝ)^2191 ≤ (8704182248519/20000000000000 : ℝ)^1679 := by
    have hnat : (5286012797 : ℕ)^2191*20000000000000^1679 ≤ 8704182248519^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286012797 10000000000 8704182248519 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195376081/1000000000 : ℝ)^2191 ≤ (2374965406869/20000000000000 : ℝ)^1679 := by
    have hnat : (195376081 : ℕ)^2191*20000000000000^1679 ≤ 2374965406869^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195376081 1000000000 2374965406869 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077311321/2000000000 : ℝ)^2191 ≤ (44604261710457/100000000000000 : ℝ)^1679 := by
    have hnat : (1077311321 : ℕ)^2191*100000000000000^1679 ≤ 44604261710457^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077311321 2000000000 44604261710457 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286012797/10000000000 : ℝ), (-195376081/1000000000 : ℝ), (1077311321/2000000000 : ℝ)] ![(8704182248519/20000000000000 : ℝ), (2374965406869/20000000000000 : ℝ), (44604261710457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286012797/10000000000 : ℝ)|^2191 ≤ (8704182248519/20000000000000 : ℝ)^1679
        have hw : |(5286012797/10000000000 : ℝ)|=(5286012797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195376081/1000000000 : ℝ)|^2191 ≤ (2374965406869/20000000000000 : ℝ)^1679
        have hw : |(-195376081/1000000000 : ℝ)|=(195376081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077311321/2000000000 : ℝ)|^2191 ≤ (44604261710457/100000000000000 : ℝ)^1679
        have hw : |(1077311321/2000000000 : ℝ)|=(1077311321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330375787/625000000 : ℝ)*x 0 + (1077311321/2000000000 : ℝ)*x 1 + (-30527517/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330375787/625000000 : ℝ)^2191 ≤ (21760454520049/50000000000000 : ℝ)^1679 := by
    have hnat : (330375787 : ℕ)^2191*50000000000000^1679 ≤ 21760454520049^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330375787 625000000 21760454520049 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077311321/2000000000 : ℝ)^2191 ≤ (44604261710457/100000000000000 : ℝ)^1679 := by
    have hnat : (1077311321 : ℕ)^2191*100000000000000^1679 ≤ 44604261710457^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077311321 2000000000 44604261710457 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30527517/156250000 : ℝ)^2191 ≤ (11874829239263/100000000000000 : ℝ)^1679 := by
    have hnat : (30527517 : ℕ)^2191*100000000000000^1679 ≤ 11874829239263^1679*156250000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30527517 156250000 11874829239263 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330375787/625000000 : ℝ), (1077311321/2000000000 : ℝ), (-30527517/156250000 : ℝ)] ![(21760454520049/50000000000000 : ℝ), (44604261710457/100000000000000 : ℝ), (11874829239263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330375787/625000000 : ℝ)|^2191 ≤ (21760454520049/50000000000000 : ℝ)^1679
        have hw : |(330375787/625000000 : ℝ)|=(330375787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077311321/2000000000 : ℝ)|^2191 ≤ (44604261710457/100000000000000 : ℝ)^1679
        have hw : |(1077311321/2000000000 : ℝ)|=(1077311321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30527517/156250000 : ℝ)|^2191 ≤ (11874829239263/100000000000000 : ℝ)^1679
        have hw : |(-30527517/156250000 : ℝ)|=(30527517/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2226284111/5000000000 : ℝ)*x 0 + (4236630561/10000000000 : ℝ)*x 1 + (2118315409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2226284111/5000000000 : ℝ)^2191 ≤ (34790181313107/100000000000000 : ℝ)^1679 := by
    have hnat : (2226284111 : ℕ)^2191*100000000000000^1679 ≤ 34790181313107^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226284111 5000000000 34790181313107 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236630561/10000000000 : ℝ)^2191 ≤ (8151227011311/25000000000000 : ℝ)^1679 := by
    have hnat : (4236630561 : ℕ)^2191*25000000000000^1679 ≤ 8151227011311^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236630561 10000000000 8151227011311 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118315409/5000000000 : ℝ)^2191 ≤ (32604910626239/100000000000000 : ℝ)^1679 := by
    have hnat : (2118315409 : ℕ)^2191*100000000000000^1679 ≤ 32604910626239^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118315409 5000000000 32604910626239 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2226284111/5000000000 : ℝ), (4236630561/10000000000 : ℝ), (2118315409/5000000000 : ℝ)] ![(34790181313107/100000000000000 : ℝ), (8151227011311/25000000000000 : ℝ), (32604910626239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2226284111/5000000000 : ℝ)|^2191 ≤ (34790181313107/100000000000000 : ℝ)^1679
        have hw : |(2226284111/5000000000 : ℝ)|=(2226284111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236630561/10000000000 : ℝ)|^2191 ≤ (8151227011311/25000000000000 : ℝ)^1679
        have hw : |(4236630561/10000000000 : ℝ)|=(4236630561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118315409/5000000000 : ℝ)|^2191 ≤ (32604910626239/100000000000000 : ℝ)^1679
        have hw : |(2118315409/5000000000 : ℝ)|=(2118315409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070365919/5000000000 : ℝ)*x 0 + (5266420267/10000000000 : ℝ)*x 1 + (2633210197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070365919/5000000000 : ℝ)^2191 ≤ (13378937890139/100000000000000 : ℝ)^1679 := by
    have hnat : (1070365919 : ℕ)^2191*100000000000000^1679 ≤ 13378937890139^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070365919 5000000000 13378937890139 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266420267/10000000000 : ℝ)^2191 ≤ (1082763259197/2500000000000 : ℝ)^1679 := by
    have hnat : (5266420267 : ℕ)^2191*2500000000000^1679 ≤ 1082763259197^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266420267 10000000000 1082763259197 2500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633210197/5000000000 : ℝ)^2191 ≤ (4331053173081/10000000000000 : ℝ)^1679 := by
    have hnat : (2633210197 : ℕ)^2191*10000000000000^1679 ≤ 4331053173081^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633210197 5000000000 4331053173081 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070365919/5000000000 : ℝ), (5266420267/10000000000 : ℝ), (2633210197/5000000000 : ℝ)] ![(13378937890139/100000000000000 : ℝ), (1082763259197/2500000000000 : ℝ), (4331053173081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070365919/5000000000 : ℝ)|^2191 ≤ (13378937890139/100000000000000 : ℝ)^1679
        have hw : |(-1070365919/5000000000 : ℝ)|=(1070365919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266420267/10000000000 : ℝ)|^2191 ≤ (1082763259197/2500000000000 : ℝ)^1679
        have hw : |(5266420267/10000000000 : ℝ)|=(5266420267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633210197/5000000000 : ℝ)|^2191 ≤ (4331053173081/10000000000000 : ℝ)^1679
        have hw : |(2633210197/5000000000 : ℝ)|=(2633210197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83908037/156250000 : ℝ)*x 0 + (-2002492973/10000000000 : ℝ)*x 1 + (2633209939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83908037/156250000 : ℝ)^2191 ≤ (8885334596549/20000000000000 : ℝ)^1679 := by
    have hnat : (83908037 : ℕ)^2191*20000000000000^1679 ≤ 8885334596549^1679*156250000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83908037 156250000 8885334596549 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002492973/10000000000 : ℝ)^2191 ≤ (12262800813719/100000000000000 : ℝ)^1679 := by
    have hnat : (2002492973 : ℕ)^2191*100000000000000^1679 ≤ 12262800813719^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002492973 10000000000 12262800813719 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633209939/5000000000 : ℝ)^2191 ≤ (21655263096619/50000000000000 : ℝ)^1679 := by
    have hnat : (2633209939 : ℕ)^2191*50000000000000^1679 ≤ 21655263096619^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633209939 5000000000 21655263096619 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83908037/156250000 : ℝ), (-2002492973/10000000000 : ℝ), (2633209939/5000000000 : ℝ)] ![(8885334596549/20000000000000 : ℝ), (12262800813719/100000000000000 : ℝ), (21655263096619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83908037/156250000 : ℝ)|^2191 ≤ (8885334596549/20000000000000 : ℝ)^1679
        have hw : |(83908037/156250000 : ℝ)|=(83908037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002492973/10000000000 : ℝ)|^2191 ≤ (12262800813719/100000000000000 : ℝ)^1679
        have hw : |(-2002492973/10000000000 : ℝ)|=(2002492973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633209939/5000000000 : ℝ)|^2191 ≤ (21655263096619/50000000000000 : ℝ)^1679
        have hw : |(2633209939/5000000000 : ℝ)|=(2633209939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370113759/10000000000 : ℝ)*x 0 + (5266421021/10000000000 : ℝ)*x 1 + (-2002492261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370113759/10000000000 : ℝ)^2191 ≤ (44426666408147/100000000000000 : ℝ)^1679 := by
    have hnat : (5370113759 : ℕ)^2191*100000000000000^1679 ≤ 44426666408147^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370113759 10000000000 44426666408147 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266421021/10000000000 : ℝ)^2191 ≤ (10827634614901/25000000000000 : ℝ)^1679 := by
    have hnat : (5266421021 : ℕ)^2191*25000000000000^1679 ≤ 10827634614901^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266421021 10000000000 10827634614901 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002492261/10000000000 : ℝ)^2191 ≤ (12262795124007/100000000000000 : ℝ)^1679 := by
    have hnat : (2002492261 : ℕ)^2191*100000000000000^1679 ≤ 12262795124007^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002492261 10000000000 12262795124007 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370113759/10000000000 : ℝ), (5266421021/10000000000 : ℝ), (-2002492261/10000000000 : ℝ)] ![(44426666408147/100000000000000 : ℝ), (10827634614901/25000000000000 : ℝ), (12262795124007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370113759/10000000000 : ℝ)|^2191 ≤ (44426666408147/100000000000000 : ℝ)^1679
        have hw : |(5370113759/10000000000 : ℝ)|=(5370113759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266421021/10000000000 : ℝ)|^2191 ≤ (10827634614901/25000000000000 : ℝ)^1679
        have hw : |(5266421021/10000000000 : ℝ)|=(5266421021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002492261/10000000000 : ℝ)|^2191 ≤ (12262795124007/100000000000000 : ℝ)^1679
        have hw : |(-2002492261/10000000000 : ℝ)|=(2002492261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4158649579/10000000000 : ℝ)*x 0 + (876707719/2000000000 : ℝ)*x 1 + (1095884809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158649579/10000000000 : ℝ)^2191 ≤ (6364793858847/20000000000000 : ℝ)^1679 := by
    have hnat : (4158649579 : ℕ)^2191*20000000000000^1679 ≤ 6364793858847^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158649579 10000000000 6364793858847 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876707719/2000000000 : ℝ)^2191 ≤ (4261001511561/12500000000000 : ℝ)^1679 := by
    have hnat : (876707719 : ℕ)^2191*12500000000000^1679 ≤ 4261001511561^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876707719 2000000000 4261001511561 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095884809/2500000000 : ℝ)^2191 ≤ (34088018597177/100000000000000 : ℝ)^1679 := by
    have hnat : (1095884809 : ℕ)^2191*100000000000000^1679 ≤ 34088018597177^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095884809 2500000000 34088018597177 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158649579/10000000000 : ℝ), (876707719/2000000000 : ℝ), (1095884809/2500000000 : ℝ)] ![(6364793858847/20000000000000 : ℝ), (4261001511561/12500000000000 : ℝ), (34088018597177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158649579/10000000000 : ℝ)|^2191 ≤ (6364793858847/20000000000000 : ℝ)^1679
        have hw : |(4158649579/10000000000 : ℝ)|=(4158649579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876707719/2000000000 : ℝ)|^2191 ≤ (4261001511561/12500000000000 : ℝ)^1679
        have hw : |(876707719/2000000000 : ℝ)|=(876707719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095884809/2500000000 : ℝ)|^2191 ≤ (34088018597177/100000000000000 : ℝ)^1679
        have hw : |(1095884809/2500000000 : ℝ)|=(1095884809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_8 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-207227663/1000000000 : ℝ)*x 0 + (5183354067/10000000000 : ℝ)*x 1 + (2700267469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207227663/1000000000 : ℝ)^2191 ≤ (12823393314549/100000000000000 : ℝ)^1679 := by
    have hnat : (207227663 : ℕ)^2191*100000000000000^1679 ≤ 12823393314549^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207227663 1000000000 12823393314549 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183354067/10000000000 : ℝ)^2191 ≤ (21210619101059/50000000000000 : ℝ)^1679 := by
    have hnat : (5183354067 : ℕ)^2191*50000000000000^1679 ≤ 21210619101059^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183354067 10000000000 21210619101059 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700267469/5000000000 : ℝ)^2191 ≤ (1118884211741/2500000000000 : ℝ)^1679 := by
    have hnat : (2700267469 : ℕ)^2191*2500000000000^1679 ≤ 1118884211741^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700267469 5000000000 1118884211741 2500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207227663/1000000000 : ℝ), (5183354067/10000000000 : ℝ), (2700267469/5000000000 : ℝ)] ![(12823393314549/100000000000000 : ℝ), (21210619101059/50000000000000 : ℝ), (1118884211741/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207227663/1000000000 : ℝ)|^2191 ≤ (12823393314549/100000000000000 : ℝ)^1679
        have hw : |(-207227663/1000000000 : ℝ)|=(207227663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183354067/10000000000 : ℝ)|^2191 ≤ (21210619101059/50000000000000 : ℝ)^1679
        have hw : |(5183354067/10000000000 : ℝ)|=(5183354067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700267469/5000000000 : ℝ)|^2191 ≤ (1118884211741/2500000000000 : ℝ)^1679
        have hw : |(2700267469/5000000000 : ℝ)|=(2700267469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_9 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638111417/5000000000 : ℝ)*x 0 + (-486991037/2500000000 : ℝ)*x 1 + (2700267487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638111417/5000000000 : ℝ)^2191 ≤ (678371229631/1562500000000 : ℝ)^1679 := by
    have hnat : (2638111417 : ℕ)^2191*1562500000000^1679 ≤ 678371229631^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638111417 5000000000 678371229631 1562500000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486991037/2500000000 : ℝ)^2191 ≤ (739304527643/6250000000000 : ℝ)^1679 := by
    have hnat : (486991037 : ℕ)^2191*6250000000000^1679 ≤ 739304527643^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486991037 2500000000 739304527643 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700267487/5000000000 : ℝ)^2191 ≤ (11188842214739/25000000000000 : ℝ)^1679 := by
    have hnat : (2700267487 : ℕ)^2191*25000000000000^1679 ≤ 11188842214739^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700267487 5000000000 11188842214739 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638111417/5000000000 : ℝ), (-486991037/2500000000 : ℝ), (2700267487/5000000000 : ℝ)] ![(678371229631/1562500000000 : ℝ), (739304527643/6250000000000 : ℝ), (11188842214739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638111417/5000000000 : ℝ)|^2191 ≤ (678371229631/1562500000000 : ℝ)^1679
        have hw : |(2638111417/5000000000 : ℝ)|=(2638111417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486991037/2500000000 : ℝ)|^2191 ≤ (739304527643/6250000000000 : ℝ)^1679
        have hw : |(-486991037/2500000000 : ℝ)|=(486991037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700267487/5000000000 : ℝ)|^2191 ≤ (11188842214739/25000000000000 : ℝ)^1679
        have hw : |(2700267487/5000000000 : ℝ)|=(2700267487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_10 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276222721/10000000000 : ℝ)*x 0 + (1080107017/2000000000 : ℝ)*x 1 + (-1947964149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276222721/10000000000 : ℝ)^2191 ≤ (4341575748301/10000000000000 : ℝ)^1679 := by
    have hnat : (5276222721 : ℕ)^2191*10000000000000^1679 ≤ 4341575748301^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276222721 10000000000 4341575748301 10000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080107017/2000000000 : ℝ)^2191 ≤ (11188842514837/25000000000000 : ℝ)^1679 := by
    have hnat : (1080107017 : ℕ)^2191*25000000000000^1679 ≤ 11188842514837^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080107017 2000000000 11188842514837 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947964149/10000000000 : ℝ)^2191 ≤ (2957218112553/25000000000000 : ℝ)^1679 := by
    have hnat : (1947964149 : ℕ)^2191*25000000000000^1679 ≤ 2957218112553^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947964149 10000000000 2957218112553 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276222721/10000000000 : ℝ), (1080107017/2000000000 : ℝ), (-1947964149/10000000000 : ℝ)] ![(4341575748301/10000000000000 : ℝ), (11188842514837/25000000000000 : ℝ), (2957218112553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276222721/10000000000 : ℝ)|^2191 ≤ (4341575748301/10000000000000 : ℝ)^1679
        have hw : |(5276222721/10000000000 : ℝ)|=(5276222721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080107017/2000000000 : ℝ)|^2191 ≤ (11188842514837/25000000000000 : ℝ)^1679
        have hw : |(1080107017/2000000000 : ℝ)|=(1080107017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947964149/10000000000 : ℝ)|^2191 ≤ (2957218112553/25000000000000 : ℝ)^1679
        have hw : |(-1947964149/10000000000 : ℝ)|=(1947964149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_11 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4486209917/10000000000 : ℝ)*x 0 + (2109761323/5000000000 : ℝ)*x 1 + (2109761397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486209917/10000000000 : ℝ)^2191 ≤ (17566796397743/50000000000000 : ℝ)^1679 := by
    have hnat : (4486209917 : ℕ)^2191*50000000000000^1679 ≤ 17566796397743^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486209917 10000000000 17566796397743 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109761323/5000000000 : ℝ)^2191 ≤ (32433202854567/100000000000000 : ℝ)^1679 := by
    have hnat : (2109761323 : ℕ)^2191*100000000000000^1679 ≤ 32433202854567^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109761323 5000000000 32433202854567 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109761397/5000000000 : ℝ)^2191 ≤ (16216602169533/50000000000000 : ℝ)^1679 := by
    have hnat : (2109761397 : ℕ)^2191*50000000000000^1679 ≤ 16216602169533^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109761397 5000000000 16216602169533 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486209917/10000000000 : ℝ), (2109761323/5000000000 : ℝ), (2109761397/5000000000 : ℝ)] ![(17566796397743/50000000000000 : ℝ), (32433202854567/100000000000000 : ℝ), (16216602169533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486209917/10000000000 : ℝ)|^2191 ≤ (17566796397743/50000000000000 : ℝ)^1679
        have hw : |(4486209917/10000000000 : ℝ)|=(4486209917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109761323/5000000000 : ℝ)|^2191 ≤ (32433202854567/100000000000000 : ℝ)^1679
        have hw : |(2109761323/5000000000 : ℝ)|=(2109761323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109761397/5000000000 : ℝ)|^2191 ≤ (16216602169533/50000000000000 : ℝ)^1679
        have hw : |(2109761397/5000000000 : ℝ)|=(2109761397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_12 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-117768981/625000000 : ℝ)*x 0 + (5467585689/10000000000 : ℝ)*x 1 + (5255297689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117768981/625000000 : ℝ)^2191 ≤ (11326948798849/100000000000000 : ℝ)^1679 := by
    have hnat : (117768981 : ℕ)^2191*100000000000000^1679 ≤ 11326948798849^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117768981 625000000 11326948798849 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467585689/10000000000 : ℝ)^2191 ≤ (11370461710473/25000000000000 : ℝ)^1679 := by
    have hnat : (5467585689 : ℕ)^2191*25000000000000^1679 ≤ 11370461710473^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467585689 10000000000 11370461710473 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255297689/10000000000 : ℝ)^2191 ≤ (21595602169369/50000000000000 : ℝ)^1679 := by
    have hnat : (5255297689 : ℕ)^2191*50000000000000^1679 ≤ 21595602169369^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255297689 10000000000 21595602169369 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117768981/625000000 : ℝ), (5467585689/10000000000 : ℝ), (5255297689/10000000000 : ℝ)] ![(11326948798849/100000000000000 : ℝ), (11370461710473/25000000000000 : ℝ), (21595602169369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117768981/625000000 : ℝ)|^2191 ≤ (11326948798849/100000000000000 : ℝ)^1679
        have hw : |(-117768981/625000000 : ℝ)|=(117768981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467585689/10000000000 : ℝ)|^2191 ≤ (11370461710473/25000000000000 : ℝ)^1679
        have hw : |(5467585689/10000000000 : ℝ)|=(5467585689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255297689/10000000000 : ℝ)|^2191 ≤ (21595602169369/50000000000000 : ℝ)^1679
        have hw : |(5255297689/10000000000 : ℝ)|=(5255297689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_13 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (672237317/1250000000 : ℝ)*x 0 + (-501726163/2500000000 : ℝ)*x 1 + (5255297801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672237317/1250000000 : ℝ)^2191 ≤ (44510727310639/100000000000000 : ℝ)^1679 := by
    have hnat : (672237317 : ℕ)^2191*100000000000000^1679 ≤ 44510727310639^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672237317 1250000000 44510727310639 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501726163/2500000000 : ℝ)^2191 ≤ (3074516781411/25000000000000 : ℝ)^1679 := by
    have hnat : (501726163 : ℕ)^2191*25000000000000^1679 ≤ 3074516781411^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501726163 2500000000 3074516781411 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255297801/10000000000 : ℝ)^2191 ≤ (43191205539917/100000000000000 : ℝ)^1679 := by
    have hnat : (5255297801 : ℕ)^2191*100000000000000^1679 ≤ 43191205539917^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255297801 10000000000 43191205539917 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672237317/1250000000 : ℝ), (-501726163/2500000000 : ℝ), (5255297801/10000000000 : ℝ)] ![(44510727310639/100000000000000 : ℝ), (3074516781411/25000000000000 : ℝ), (43191205539917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672237317/1250000000 : ℝ)|^2191 ≤ (44510727310639/100000000000000 : ℝ)^1679
        have hw : |(672237317/1250000000 : ℝ)|=(672237317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501726163/2500000000 : ℝ)|^2191 ≤ (3074516781411/25000000000000 : ℝ)^1679
        have hw : |(-501726163/2500000000 : ℝ)|=(501726163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255297801/10000000000 : ℝ)|^2191 ≤ (43191205539917/100000000000000 : ℝ)^1679
        have hw : |(5255297801/10000000000 : ℝ)|=(5255297801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_14 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268894927/500000000 : ℝ)*x 0 + (5255297803/10000000000 : ℝ)*x 1 + (-1003452323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268894927/500000000 : ℝ)^2191 ≤ (44510727353841/100000000000000 : ℝ)^1679 := by
    have hnat : (268894927 : ℕ)^2191*100000000000000^1679 ≤ 44510727353841^1679*500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268894927 500000000 44510727353841 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255297803/10000000000 : ℝ)^2191 ≤ (21595602780683/50000000000000 : ℝ)^1679 := by
    have hnat : (5255297803 : ℕ)^2191*50000000000000^1679 ≤ 21595602780683^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255297803 10000000000 21595602780683 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003452323/5000000000 : ℝ)^2191 ≤ (2459613415533/20000000000000 : ℝ)^1679 := by
    have hnat : (1003452323 : ℕ)^2191*20000000000000^1679 ≤ 2459613415533^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003452323 5000000000 2459613415533 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268894927/500000000 : ℝ), (5255297803/10000000000 : ℝ), (-1003452323/5000000000 : ℝ)] ![(44510727353841/100000000000000 : ℝ), (21595602780683/50000000000000 : ℝ), (2459613415533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268894927/500000000 : ℝ)|^2191 ≤ (44510727353841/100000000000000 : ℝ)^1679
        have hw : |(268894927/500000000 : ℝ)|=(268894927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255297803/10000000000 : ℝ)|^2191 ≤ (21595602780683/50000000000000 : ℝ)^1679
        have hw : |(5255297803/10000000000 : ℝ)|=(5255297803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003452323/5000000000 : ℝ)|^2191 ≤ (2459613415533/20000000000000 : ℝ)^1679
        have hw : |(-1003452323/5000000000 : ℝ)|=(1003452323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_box_15 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (64546689/156250000 : ℝ)*x 0 + (2198564431/5000000000 : ℝ)*x 1 + (2198564633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64546689/156250000 : ℝ)^2191 ≤ (15774010470621/50000000000000 : ℝ)^1679 := by
    have hnat : (64546689 : ℕ)^2191*50000000000000^1679 ≤ 15774010470621^1679*156250000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64546689 156250000 15774010470621 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198564431/5000000000 : ℝ)^2191 ≤ (8556496868983/25000000000000 : ℝ)^1679 := by
    have hnat : (2198564431 : ℕ)^2191*25000000000000^1679 ≤ 8556496868983^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198564431 5000000000 8556496868983 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198564633/5000000000 : ℝ)^2191 ≤ (34225991579483/100000000000000 : ℝ)^1679 := by
    have hnat : (2198564633 : ℕ)^2191*100000000000000^1679 ≤ 34225991579483^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198564633 5000000000 34225991579483 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64546689/156250000 : ℝ), (2198564431/5000000000 : ℝ), (2198564633/5000000000 : ℝ)] ![(15774010470621/50000000000000 : ℝ), (8556496868983/25000000000000 : ℝ), (34225991579483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64546689/156250000 : ℝ)|^2191 ≤ (15774010470621/50000000000000 : ℝ)^1679
        have hw : |(64546689/156250000 : ℝ)|=(64546689/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198564431/5000000000 : ℝ)|^2191 ≤ (8556496868983/25000000000000 : ℝ)^1679
        have hw : |(2198564431/5000000000 : ℝ)|=(2198564431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2198564633/5000000000 : ℝ)|^2191 ≤ (34225991579483/100000000000000 : ℝ)^1679
        have hw : |(2198564633/5000000000 : ℝ)|=(2198564633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12579/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59099/100000 : ℝ) ∧ (8041/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84659/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5663/50000 : ℝ) ^ (4381/1024 : ℝ) ≤ (8975042648646757/100000000000000000000 : ℝ) := by
    have hpowers : (5663/50000 : ℝ)^4381 ≤ (8975042648646757/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5663 : ℕ)^4381*100000000000000000000^1024 ≤ 8975042648646757^1024*50000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5663 50000 8975042648646757 100000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5663/50000 : ℝ)) (X := (8975042648646757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4381/1024 : ℝ) ≤ (1112407422862509/4000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4381 ≤ (1112407422862509/4000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4381*4000000000000000000^1024 ≤ 1112407422862509^1024*100000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 1112407422862509 4000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (1112407422862509/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008975042648646757/50000000000000000000 : ℝ) ≤ (5000209765160683/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50008975042648646757/50000000000000000000 : ℝ)^1024 ≤ (5000209765160683/5000000000000000 : ℝ)^4381 := by
      have hnat : (50008975042648646757 : ℕ)^1024*5000000000000000^4381 ≤ 5000209765160683^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008975042648646757 50000000000000000000 5000209765160683 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000209765160683/5000000000000000 : ℝ)) (X := (50008975042648646757/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018392614110104741/50000000000000000000 : ℝ) ≤ (1000085968422881/1000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50018392614110104741/50000000000000000000 : ℝ)^1024 ≤ (1000085968422881/1000000000000000 : ℝ)^4381 := by
      have hnat : (50018392614110104741 : ℕ)^1024*1000000000000000^4381 ≤ 1000085968422881^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018392614110104741 50000000000000000000 1000085968422881 1000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000085968422881/1000000000000000 : ℝ)) (X := (50018392614110104741/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001112407422862509/2000000000000000000 : ℝ) ≤ (5000649919068127/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (2001112407422862509/2000000000000000000 : ℝ)^1024 ≤ (5000649919068127/5000000000000000 : ℝ)^4381 := by
      have hnat : (2001112407422862509 : ℕ)^1024*5000000000000000^4381 ≤ 5000649919068127^4381*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001112407422862509 2000000000000000000 5000649919068127 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000649919068127/5000000000000000 : ℝ)) (X := (2001112407422862509/2000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8975042648646757/100000000000000000000 : ℝ) ≤ ((17130733682049949897/17135000000000000000 : ℝ)+2*(110038476861/85675000000000 : ℝ)*(5663/50000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (17130733682049949897/17135000000000000000 : ℝ)+2*(110038476861/85675000000000 : ℝ)*(5663/50000 : ℝ)=(5000209765160683/5000000000000000 : ℝ) by norm_num, show 1+2*(8975042648646757/100000000000000000000 : ℝ)=(50008975042648646757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1112407422862509/4000000000000000000 : ℝ)+(8975042648646757/100000000000000000000 : ℝ) ≤ ((17130733682049949897/17135000000000000000 : ℝ)+(110038476861/85675000000000 : ℝ)*((14753/100000 : ℝ)+(5663/50000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (17130733682049949897/17135000000000000000 : ℝ)+(110038476861/85675000000000 : ℝ)*((14753/100000 : ℝ)+(5663/50000 : ℝ))=(1000085968422881/1000000000000000 : ℝ) by norm_num, show 1+(1112407422862509/4000000000000000000 : ℝ)+(8975042648646757/100000000000000000000 : ℝ)=(50018392614110104741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1112407422862509/4000000000000000000 : ℝ) ≤ ((17130733682049949897/17135000000000000000 : ℝ)+2*(110038476861/85675000000000 : ℝ)*(14753/100000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (17130733682049949897/17135000000000000000 : ℝ)+2*(110038476861/85675000000000 : ℝ)*(14753/100000 : ℝ)=(5000649919068127/5000000000000000 : ℝ) by norm_num, show 1+2*(1112407422862509/4000000000000000000 : ℝ)=(2001112407422862509/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17130733682049949897/17135000000000000000 : ℝ)*(X 1 0+X 2 0)+(110038476861/85675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (17130733682049949897/17135000000000000000 : ℝ)) (alpha := (110038476861/85675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17130733682049949897/17135000000000000000 : ℝ)*(X 0 1+X 2 1)+(110038476861/85675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (17130733682049949897/17135000000000000000 : ℝ)) (alpha := (110038476861/85675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17130733682049949897/17135000000000000000 : ℝ)*(X 0 2+X 1 2)+(110038476861/85675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (17130733682049949897/17135000000000000000 : ℝ)) (alpha := (110038476861/85675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-907828163/5000000000 : ℝ)*X 0 0+(5386556789/10000000000 : ℝ)*X 0 1+(5386556507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286012797/10000000000 : ℝ)*X 1 0+(-195376081/1000000000 : ℝ)*X 1 1+(1077311321/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((330375787/625000000 : ℝ)*X 2 0+(1077311321/2000000000 : ℝ)*X 2 1+(-30527517/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2226284111/5000000000 : ℝ)*X 0 0+(4236630561/10000000000 : ℝ)*X 0 1+(2118315409/5000000000 : ℝ)*X 0 2+(2226284111/5000000000 : ℝ)*X 1 0+(4236630561/10000000000 : ℝ)*X 1 1+(2118315409/5000000000 : ℝ)*X 1 2+(2226284111/5000000000 : ℝ)*X 2 0+(4236630561/10000000000 : ℝ)*X 2 1+(2118315409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070365919/5000000000 : ℝ)*X 0 0+(5266420267/10000000000 : ℝ)*X 0 1+(2633210197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((83908037/156250000 : ℝ)*X 1 0+(-2002492973/10000000000 : ℝ)*X 1 1+(2633209939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370113759/10000000000 : ℝ)*X 2 0+(5266421021/10000000000 : ℝ)*X 2 1+(-2002492261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4158649579/10000000000 : ℝ)*X 0 0+(876707719/2000000000 : ℝ)*X 0 1+(1095884809/2500000000 : ℝ)*X 0 2+(4158649579/10000000000 : ℝ)*X 1 0+(876707719/2000000000 : ℝ)*X 1 1+(1095884809/2500000000 : ℝ)*X 1 2+(4158649579/10000000000 : ℝ)*X 2 0+(876707719/2000000000 : ℝ)*X 2 1+(1095884809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-207227663/1000000000 : ℝ)*X 0 0+(5183354067/10000000000 : ℝ)*X 0 1+(2700267469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638111417/5000000000 : ℝ)*X 1 0+(-486991037/2500000000 : ℝ)*X 1 1+(2700267487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276222721/10000000000 : ℝ)*X 2 0+(1080107017/2000000000 : ℝ)*X 2 1+(-1947964149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4486209917/10000000000 : ℝ)*X 0 0+(2109761323/5000000000 : ℝ)*X 0 1+(2109761397/5000000000 : ℝ)*X 0 2+(4486209917/10000000000 : ℝ)*X 1 0+(2109761323/5000000000 : ℝ)*X 1 1+(2109761397/5000000000 : ℝ)*X 1 2+(4486209917/10000000000 : ℝ)*X 2 0+(2109761323/5000000000 : ℝ)*X 2 1+(2109761397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-117768981/625000000 : ℝ)*X 0 0+(5467585689/10000000000 : ℝ)*X 0 1+(5255297689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672237317/1250000000 : ℝ)*X 1 0+(-501726163/2500000000 : ℝ)*X 1 1+(5255297801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268894927/500000000 : ℝ)*X 2 0+(5255297803/10000000000 : ℝ)*X 2 1+(-1003452323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((64546689/156250000 : ℝ)*X 0 0+(2198564431/5000000000 : ℝ)*X 0 1+(2198564633/5000000000 : ℝ)*X 0 2+(64546689/156250000 : ℝ)*X 1 0+(2198564431/5000000000 : ℝ)*X 1 1+(2198564633/5000000000 : ℝ)*X 1 2+(64546689/156250000 : ℝ)*X 2 0+(2198564431/5000000000 : ℝ)*X 2 1+(2198564633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12579/20000 : ℝ) ≤ (-134708292109482203624305903985667/214187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83415307/100000000000000 : ℝ)*(lower1) + (41904017/50000000000000 : ℝ)*(lower2) + (9365543/6250000000000 : ℝ)*(lower3) + (3652739/25000000000000 : ℝ)*(lower4) + (1504564362570637/50000000000000 : ℝ)*(major0) + (1504564362570637/50000000000000 : ℝ)*(major1) + (1504564362570637/50000000000000 : ℝ)*(major2) + (3055867933/25000000000000 : ℝ)*(sp1) + (2066687688233543/50000000000000 : ℝ)*(sp4) + (2066681576497677/50000000000000 : ℝ)*(sp5) + (2066547595455139/50000000000000 : ℝ)*(sp6) + (381162477658981/20000000000000 : ℝ)*(sp7) + (280185556807/100000000000000 : ℝ)*(sp14) + (3391734383/10000000000000 : ℝ)*(sp15) + (381169261127747/20000000000000 : ℝ)*(f.failure) + (2066687688233543/50000000000000 : ℝ)*(f.sum) + (74016216987289/17135000000000000000000000000 : ℝ)*base66 + (5891195521310024389/856750000000000000000000000000000 : ℝ)*base67 + (4397313662267774389/856750000000000000000000000000000 : ℝ)*base69 + (2650371901904475611/856750000000000000000000000000000 : ℝ)*base72 + (41592754710301/17135000000000000000000000000 : ℝ)*base73 + (2510334820148774389/856750000000000000000000000000000 : ℝ)*base75 + (10027578044280024389/856750000000000000000000000000000 : ℝ)*base77 + (6084720869805274389/856750000000000000000000000000000 : ℝ)*base79 + (4088762970241/1070937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1665061/200000000000000000000 : ℝ)*base90 + (1665061/200000000000000000000 : ℝ)*base92 + (1665061/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59099/100000 : ℝ) ≤ (15823527625385389832179367437851/26773437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (691629/10000000000000 : ℝ)*(lower1) + (182721/625000000000 : ℝ)*(upper2) + (101737151/100000000000000 : ℝ)*(lower4) + (46878003/100000000000000 : ℝ)*(lower5) + (48132962237341/1562500000000 : ℝ)*(major0) + (48132962237341/1562500000000 : ℝ)*(major1) + (48132962237341/1562500000000 : ℝ)*(major2) + (4190262916854143/100000000000000 : ℝ)*(sp0) + (209513003720111/5000000000000 : ℝ)*(sp1) + (2095120647940379/50000000000000 : ℝ)*(sp2) + (1951054837331379/100000000000000 : ℝ)*(sp3) + (710612981/25000000000000 : ℝ)*(sp5) + (4408697/500000000000 : ℝ)*(sp7) + (4324194677/20000000000000 : ℝ)*(sp10) + (1951055719070779/100000000000000 : ℝ)*(f.failure) + (4190262916854143/100000000000000 : ℝ)*(f.sum) + (9480401021707/2141875000000000000000000000 : ℝ)*base65 + (7961777735984563/6693359375000000000000000000000 : ℝ)*base67 + (285129212330392129/53546875000000000000000000000000 : ℝ)*base69 + (2907115619828031/3346679687500000000000000000000 : ℝ)*base72 + (10469820481311/17135000000000000000000000000 : ℝ)*base73 + (65471799536047251/13386718750000000000000000000000 : ℝ)*base75 + (268077684626142129/53546875000000000000000000000000 : ℝ)*base77 + (6438863644750047/1673339843750000000000000000000 : ℝ)*base79 + (117204952306201/17135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11828077/1000000000000000000000 : ℝ)*base90 + (11828077/1000000000000000000000 : ℝ)*base92 + (11828077/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (8041/10000 : ℝ) ≤ (688932455016476268157625127265653/856750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4183693/12500000000000 : ℝ)*(upper0) + (70085661/100000000000000 : ℝ)*(upper2) + (5392101/25000000000000 : ℝ)*(upper3) + (50824741/100000000000000 : ℝ)*(upper4) + (3388781691324383/100000000000000 : ℝ)*(major0) + (3388781691324383/100000000000000 : ℝ)*(major1) + (3388781691324383/100000000000000 : ℝ)*(major2) + (446433809/12500000000000 : ℝ)*(sp0) + (4184101639/12500000000000 : ℝ)*(sp2) + (28572334057/100000000000000 : ℝ)*(sp3) + (4604454350980789/100000000000000 : ℝ)*(sp8) + (2302228961225631/50000000000000 : ℝ)*(sp9) + (4604424449638149/100000000000000 : ℝ)*(sp10) + (53656819623863/2500000000000 : ℝ)*(sp11) + (2146301357288577/100000000000000 : ℝ)*(f.failure) + (2302228961225631/50000000000000 : ℝ)*(f.sum) + (82154023497867/4283750000000000000000000000 : ℝ)*base66 + (2482529764290961449/1713500000000000000000000000000000 : ℝ)*base68 + (2204002872635038551/1713500000000000000000000000000000 : ℝ)*base69 + (44049124816349961449/1713500000000000000000000000000000 : ℝ)*base72 + (40785389501283/17135000000000000000000000000 : ℝ)*base74 + (4941583083091961449/1713500000000000000000000000000000 : ℝ)*base76 + (4168125662612538551/1713500000000000000000000000000000 : ℝ)*base77 + (2202388199669961449/1713500000000000000000000000000000 : ℝ)*base80 + (101100081071563/17135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3072649/1000000000000000000000 : ℝ)*base89 + (3072649/1000000000000000000000 : ℝ)*base91 + (3072649/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84659/100000 : ℝ) ≤ (-725290335330468706464564037024533/856750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10618969/50000000000000 : ℝ)*(lower1) + (6019879/20000000000000 : ℝ)*(upper3) + (7492953/20000000000000 : ℝ)*(lower4) + (60829347/50000000000000 : ℝ)*(upper5) + (3426173852215937/100000000000000 : ℝ)*(major0) + (3426173852215937/100000000000000 : ℝ)*(major1) + (3426173852215937/100000000000000 : ℝ)*(major2) + (638869131/50000000000000 : ℝ)*(sp4) + (25273028349/50000000000000 : ℝ)*(sp6) + (28308238853/100000000000000 : ℝ)*(sp7) + (1177645307839507/25000000000000 : ℝ)*(sp12) + (471058250909629/10000000000000 : ℝ)*(sp13) + (4710531963039591/100000000000000 : ℝ)*(sp14) + (542488888979029/25000000000000 : ℝ)*(sp15) + (2169983864154969/100000000000000 : ℝ)*(f.failure) + (471058250909629/10000000000000 : ℝ)*(f.sum) + (100212213309863/17135000000000000000000000000 : ℝ)*base65 + (13820686012509191511/1713500000000000000000000000000000 : ℝ)*base68 + (6021282591492308489/1713500000000000000000000000000000 : ℝ)*base69 + (11356657059824191511/1713500000000000000000000000000000 : ℝ)*base72 + (1313337974317/17135000000000000000000000000 : ℝ)*base74 + (2997460385402691511/1713500000000000000000000000000000 : ℝ)*base76 + (893199878768808489/1713500000000000000000000000000000 : ℝ)*base77 + (15273511806691511/1713500000000000000000000000000000 : ℝ)*base80 + (86991185338257/4283750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6222047/1000000000000000000000 : ℝ)*base90 + (6222047/1000000000000000000000 : ℝ)*base92 + (6222047/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1422_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59099/100000 : ℝ) else (8041/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84659/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1422_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1422_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59099/100000 : ℝ) else (8041/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84659/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1422_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1422_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59099/100000 : ℝ) else (8041/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84659/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
