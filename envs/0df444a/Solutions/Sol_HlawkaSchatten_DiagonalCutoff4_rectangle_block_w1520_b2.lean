-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:12.99198+00:00
-- url     : https://prove2.me/submissions/fbbe1957-f7be-416c-807a-5dac748e7eae

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
theorem support_rectangle_w1520_s6_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351142457/10000000000 : ℝ)*x 0 + (2609015597/5000000000 : ℝ)*x 1 + (-491482237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351142457/10000000000 : ℝ)^4537 ≤ (22297785277267/50000000000000 : ℝ)^3513 := by
    have hnat : (5351142457 : ℕ)^4537*50000000000000^3513 ≤ 22297785277267^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351142457 10000000000 22297785277267 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609015597/5000000000 : ℝ)^4537 ≤ (43168110728631/100000000000000 : ℝ)^3513 := by
    have hnat : (2609015597 : ℕ)^4537*100000000000000^3513 ≤ 43168110728631^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609015597 5000000000 43168110728631 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491482237/2500000000 : ℝ)^4537 ≤ (12236318692493/100000000000000 : ℝ)^3513 := by
    have hnat : (491482237 : ℕ)^4537*100000000000000^3513 ≤ 12236318692493^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491482237 2500000000 12236318692493 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351142457/10000000000 : ℝ), (2609015597/5000000000 : ℝ), (-491482237/2500000000 : ℝ)] ![(22297785277267/50000000000000 : ℝ), (43168110728631/100000000000000 : ℝ), (12236318692493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351142457/10000000000 : ℝ)|^4537 ≤ (22297785277267/50000000000000 : ℝ)^3513
        have hw : |(5351142457/10000000000 : ℝ)|=(5351142457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609015597/5000000000 : ℝ)|^4537 ≤ (43168110728631/100000000000000 : ℝ)^3513
        have hw : |(2609015597/5000000000 : ℝ)|=(2609015597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491482237/2500000000 : ℝ)|^4537 ≤ (12236318692493/100000000000000 : ℝ)^3513
        have hw : |(-491482237/2500000000 : ℝ)|=(491482237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s6_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1856291383/10000000000 : ℝ)*x 0 + (1043827081/2000000000 : ℝ)*x 1 + (5431081961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856291383/10000000000 : ℝ)^4537 ≤ (11362260036199/100000000000000 : ℝ)^3513 := by
    have hnat : (1856291383 : ℕ)^4537*100000000000000^3513 ≤ 11362260036199^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856291383 10000000000 11362260036199 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043827081/2000000000 : ℝ)^4537 ≤ (43179908839231/100000000000000 : ℝ)^3513 := by
    have hnat : (1043827081 : ℕ)^4537*100000000000000^3513 ≤ 43179908839231^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043827081 2000000000 43179908839231 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431081961/10000000000 : ℝ)^4537 ≤ (1420557222169/3125000000000 : ℝ)^3513 := by
    have hnat : (5431081961 : ℕ)^4537*3125000000000^3513 ≤ 1420557222169^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431081961 10000000000 1420557222169 3125000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1856291383/10000000000 : ℝ), (1043827081/2000000000 : ℝ), (5431081961/10000000000 : ℝ)] ![(11362260036199/100000000000000 : ℝ), (43179908839231/100000000000000 : ℝ), (1420557222169/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1856291383/10000000000 : ℝ)|^4537 ≤ (11362260036199/100000000000000 : ℝ)^3513
        have hw : |(-1856291383/10000000000 : ℝ)|=(1856291383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043827081/2000000000 : ℝ)|^4537 ≤ (43179908839231/100000000000000 : ℝ)^3513
        have hw : |(1043827081/2000000000 : ℝ)|=(1043827081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431081961/10000000000 : ℝ)|^4537 ≤ (1420557222169/3125000000000 : ℝ)^3513
        have hw : |(5431081961/10000000000 : ℝ)|=(5431081961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s6_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323713699/2500000000 : ℝ)*x 0 + (-1752877813/10000000000 : ℝ)*x 1 + (2715541249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323713699/2500000000 : ℝ)^4537 ≤ (21995337028349/50000000000000 : ℝ)^3513 := by
    have hnat : (1323713699 : ℕ)^4537*50000000000000^3513 ≤ 21995337028349^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323713699 2500000000 21995337028349 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1752877813/10000000000 : ℝ)^4537 ≤ (10551489022319/100000000000000 : ℝ)^3513 := by
    have hnat : (1752877813 : ℕ)^4537*100000000000000^3513 ≤ 10551489022319^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752877813 10000000000 10551489022319 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715541249/5000000000 : ℝ)^4537 ≤ (1420557403569/3125000000000 : ℝ)^3513 := by
    have hnat : (2715541249 : ℕ)^4537*3125000000000^3513 ≤ 1420557403569^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715541249 5000000000 1420557403569 3125000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323713699/2500000000 : ℝ), (-1752877813/10000000000 : ℝ), (2715541249/5000000000 : ℝ)] ![(21995337028349/50000000000000 : ℝ), (10551489022319/100000000000000 : ℝ), (1420557403569/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323713699/2500000000 : ℝ)|^4537 ≤ (21995337028349/50000000000000 : ℝ)^3513
        have hw : |(1323713699/2500000000 : ℝ)|=(1323713699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1752877813/10000000000 : ℝ)|^4537 ≤ (10551489022319/100000000000000 : ℝ)^3513
        have hw : |(-1752877813/10000000000 : ℝ)|=(1752877813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715541249/5000000000 : ℝ)|^4537 ≤ (1420557403569/3125000000000 : ℝ)^3513
        have hw : |(2715541249/5000000000 : ℝ)|=(2715541249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s6_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661856869/1250000000 : ℝ)*x 0 + (5431082261/10000000000 : ℝ)*x 1 + (-1752877927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661856869/1250000000 : ℝ)^4537 ≤ (5498834466321/12500000000000 : ℝ)^3513 := by
    have hnat : (661856869 : ℕ)^4537*12500000000000^3513 ≤ 5498834466321^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661856869 1250000000 5498834466321 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431082261/10000000000 : ℝ)^4537 ≤ (45457834352313/100000000000000 : ℝ)^3513 := by
    have hnat : (5431082261 : ℕ)^4537*100000000000000^3513 ≤ 45457834352313^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431082261 10000000000 45457834352313 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752877927/10000000000 : ℝ)^4537 ≤ (2637872477143/25000000000000 : ℝ)^3513 := by
    have hnat : (1752877927 : ℕ)^4537*25000000000000^3513 ≤ 2637872477143^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752877927 10000000000 2637872477143 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661856869/1250000000 : ℝ), (5431082261/10000000000 : ℝ), (-1752877927/10000000000 : ℝ)] ![(5498834466321/12500000000000 : ℝ), (45457834352313/100000000000000 : ℝ), (2637872477143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661856869/1250000000 : ℝ)|^4537 ≤ (5498834466321/12500000000000 : ℝ)^3513
        have hw : |(661856869/1250000000 : ℝ)|=(661856869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431082261/10000000000 : ℝ)|^4537 ≤ (45457834352313/100000000000000 : ℝ)^3513
        have hw : |(5431082261/10000000000 : ℝ)|=(5431082261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752877927/10000000000 : ℝ)|^4537 ≤ (2637872477143/25000000000000 : ℝ)^3513
        have hw : |(-1752877927/10000000000 : ℝ)|=(1752877927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s6_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853225227/2000000000 : ℝ)*x 0 + (70525371/156250000 : ℝ)*x 1 + (1007576459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853225227/2000000000 : ℝ)^4537 ≤ (33280716911731/100000000000000 : ℝ)^3513 := by
    have hnat : (853225227 : ℕ)^4537*100000000000000^3513 ≤ 33280716911731^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853225227 2000000000 33280716911731 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70525371/156250000 : ℝ)^4537 ≤ (35795083385683/100000000000000 : ℝ)^3513 := by
    have hnat : (70525371 : ℕ)^4537*100000000000000^3513 ≤ 35795083385683^3513*156250000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70525371 156250000 35795083385683 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007576459/2500000000 : ℝ)^4537 ≤ (30924199687127/100000000000000 : ℝ)^3513 := by
    have hnat : (1007576459 : ℕ)^4537*100000000000000^3513 ≤ 30924199687127^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007576459 2500000000 30924199687127 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853225227/2000000000 : ℝ), (70525371/156250000 : ℝ), (1007576459/2500000000 : ℝ)] ![(33280716911731/100000000000000 : ℝ), (35795083385683/100000000000000 : ℝ), (30924199687127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853225227/2000000000 : ℝ)|^4537 ≤ (33280716911731/100000000000000 : ℝ)^3513
        have hw : |(853225227/2000000000 : ℝ)|=(853225227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70525371/156250000 : ℝ)|^4537 ≤ (35795083385683/100000000000000 : ℝ)^3513
        have hw : |(70525371/156250000 : ℝ)|=(70525371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007576459/2500000000 : ℝ)|^4537 ≤ (30924199687127/100000000000000 : ℝ)^3513
        have hw : |(1007576459/2500000000 : ℝ)|=(1007576459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5473/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5473/50000 : ℝ) ^ (4535/1024 : ℝ) ≤ (2780417928139751/50000000000000000000 : ℝ) := by
    have hpowers : (5473/50000 : ℝ)^4535 ≤ (2780417928139751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5473 : ℕ)^4535*50000000000000000000^1024 ≤ 2780417928139751^1024*50000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5473 50000 2780417928139751 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5473/50000 : ℝ)) (X := (2780417928139751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4535/1024 : ℝ) ≤ (12918042412885661/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4535 ≤ (12918042412885661/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4535*50000000000000000000^1024 ≤ 12918042412885661^1024*25000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 12918042412885661 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (12918042412885661/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002780417928139751/25000000000000000000 : ℝ) ≤ (10000251115800749/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25002780417928139751/25000000000000000000 : ℝ)^1024 ≤ (10000251115800749/10000000000000000 : ℝ)^4535 := by
      have hnat : (25002780417928139751 : ℕ)^1024*10000000000000000^4535 ≤ 10000251115800749^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002780417928139751 25000000000000000000 10000251115800749 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000251115800749/10000000000000000 : ℝ)) (X := (25002780417928139751/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503924615085256353/12500000000000000000 : ℝ) ≤ (7813053792379/7812500000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (12503924615085256353/12500000000000000000 : ℝ)^1024 ≤ (7813053792379/7812500000000 : ℝ)^4535 := by
      have hnat : (12503924615085256353 : ℕ)^1024*7812500000000^4535 ≤ 7813053792379^4535*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503924615085256353 12500000000000000000 7813053792379 7812500000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7813053792379/7812500000000 : ℝ)) (X := (12503924615085256353/12500000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012918042412885661/25000000000000000000 : ℝ) ≤ (10001166592689491/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25012918042412885661/25000000000000000000 : ℝ)^1024 ≤ (10001166592689491/10000000000000000 : ℝ)^4535 := by
      have hnat : (25012918042412885661 : ℕ)^1024*10000000000000000^4535 ≤ 10001166592689491^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012918042412885661 25000000000000000000 10001166592689491 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166592689491/10000000000000000 : ℝ)) (X := (25012918042412885661/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2780417928139751/50000000000000000000 : ℝ) ≤ ((4537111875347962903/4538000000000000000 : ℝ)+2*(457738444371/453800000000000 : ℝ)*(5473/50000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (4537111875347962903/4538000000000000000 : ℝ)+2*(457738444371/453800000000000 : ℝ)*(5473/50000 : ℝ)=(10000251115800749/10000000000000000 : ℝ) by norm_num, show 1+2*(2780417928139751/50000000000000000000 : ℝ)=(25002780417928139751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12918042412885661/50000000000000000000 : ℝ)+(2780417928139751/50000000000000000000 : ℝ) ≤ ((4537111875347962903/4538000000000000000 : ℝ)+(457738444371/453800000000000 : ℝ)*((3871/25000 : ℝ)+(5473/50000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (4537111875347962903/4538000000000000000 : ℝ)+(457738444371/453800000000000 : ℝ)*((3871/25000 : ℝ)+(5473/50000 : ℝ))=(7813053792379/7812500000000 : ℝ) by norm_num, show 1+(12918042412885661/50000000000000000000 : ℝ)+(2780417928139751/50000000000000000000 : ℝ)=(12503924615085256353/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12918042412885661/50000000000000000000 : ℝ) ≤ ((4537111875347962903/4538000000000000000 : ℝ)+2*(457738444371/453800000000000 : ℝ)*(3871/25000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (4537111875347962903/4538000000000000000 : ℝ)+2*(457738444371/453800000000000 : ℝ)*(3871/25000 : ℝ)=(10001166592689491/10000000000000000 : ℝ) by norm_num, show 1+2*(12918042412885661/50000000000000000000 : ℝ)=(25012918042412885661/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4537111875347962903/4538000000000000000 : ℝ)*(X 1 0+X 2 0)+(457738444371/453800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (4537111875347962903/4538000000000000000 : ℝ)) (alpha := (457738444371/453800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4537111875347962903/4538000000000000000 : ℝ)*(X 0 1+X 2 1)+(457738444371/453800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (4537111875347962903/4538000000000000000 : ℝ)) (alpha := (457738444371/453800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4537111875347962903/4538000000000000000 : ℝ)*(X 0 2+X 1 2)+(457738444371/453800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (4537111875347962903/4538000000000000000 : ℝ)) (alpha := (457738444371/453800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5351142457/10000000000 : ℝ)*X 2 0+(2609015597/5000000000 : ℝ)*X 2 1+(-491482237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1856291383/10000000000 : ℝ)*X 0 0+(1043827081/2000000000 : ℝ)*X 0 1+(5431081961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323713699/2500000000 : ℝ)*X 1 0+(-1752877813/10000000000 : ℝ)*X 1 1+(2715541249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((661856869/1250000000 : ℝ)*X 2 0+(5431082261/10000000000 : ℝ)*X 2 1+(-1752877927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((853225227/2000000000 : ℝ)*X 0 0+(70525371/156250000 : ℝ)*X 0 1+(1007576459/2500000000 : ℝ)*X 0 2+(853225227/2000000000 : ℝ)*X 1 0+(70525371/156250000 : ℝ)*X 1 1+(1007576459/2500000000 : ℝ)*X 1 2+(853225227/2000000000 : ℝ)*X 2 0+(70525371/156250000 : ℝ)*X 2 1+(1007576459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48476367613916633437003899/5672500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311132239/25000000000000 : ℝ)*(base19) + (1626621791/100000000000000 : ℝ)*(base23) + (573136421/100000000000000 : ℝ)*(lower1) + (22391611/20000000000000 : ℝ)*(upper2) + (248842699/100000000000000 : ℝ)*(upper3) + (21018157/12500000000000 : ℝ)*(upper5) + (84839504304089/2500000000000 : ℝ)*(major0) + (84839504304089/2500000000000 : ℝ)*(major1) + (84839504304089/2500000000000 : ℝ)*(major2) + (2976077507/100000000000000 : ℝ)*(sp0) + (4718139737859129/100000000000000 : ℝ)*(sp1) + (4718138493330173/100000000000000 : ℝ)*(sp2) + (589766891894979/12500000000000 : ℝ)*(sp3) + (413804064321223/20000000000000 : ℝ)*(sp4) + (413804064321223/20000000000000 : ℝ)*(f.failure) + (4718139737859129/100000000000000 : ℝ)*(f.sum) + (7413223347167/1134500000000000000000000000 : ℝ)*base65 + (125549562180675367/11345000000000000000000000000000 : ℝ)*base67 + (255711668458204633/11345000000000000000000000000000 : ℝ)*base70 + (2205378615015367/11345000000000000000000000000000 : ℝ)*base71 + (1671436367017/2269000000000000000000000000 : ℝ)*base73 + (106823023142970367/11345000000000000000000000000000 : ℝ)*base75 + (21644547656040367/11345000000000000000000000000000 : ℝ)*base77 + (92232816020749633/11345000000000000000000000000000 : ℝ)*base80 + (11154349111621/567250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14093569/2000000000000000000000 : ℝ)*base90 + (14093569/2000000000000000000000 : ℝ)*base92 + (14093569/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1520_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_s7_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1856264767/10000000000 : ℝ)*x 0 + (5432190721/10000000000 : ℝ)*x 1 + (521803333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856264767/10000000000 : ℝ)^4537 ≤ (11362049633607/100000000000000 : ℝ)^3513 := by
    have hnat : (1856264767 : ℕ)^4537*100000000000000^3513 ≤ 11362049633607^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856264767 10000000000 11362049633607 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432190721/10000000000 : ℝ)^4537 ≤ (2273490840541/5000000000000 : ℝ)^3513 := by
    have hnat : (5432190721 : ℕ)^4537*5000000000000^3513 ≤ 2273490840541^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432190721 10000000000 2273490840541 5000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521803333/1000000000 : ℝ)^4537 ≤ (21584066775173/50000000000000 : ℝ)^3513 := by
    have hnat : (521803333 : ℕ)^4537*50000000000000^3513 ≤ 21584066775173^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521803333 1000000000 21584066775173 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1856264767/10000000000 : ℝ), (5432190721/10000000000 : ℝ), (521803333/1000000000 : ℝ)] ![(11362049633607/100000000000000 : ℝ), (2273490840541/5000000000000 : ℝ), (21584066775173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1856264767/10000000000 : ℝ)|^4537 ≤ (11362049633607/100000000000000 : ℝ)^3513
        have hw : |(-1856264767/10000000000 : ℝ)|=(1856264767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432190721/10000000000 : ℝ)|^4537 ≤ (2273490840541/5000000000000 : ℝ)^3513
        have hw : |(5432190721/10000000000 : ℝ)|=(5432190721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521803333/1000000000 : ℝ)|^4537 ≤ (21584066775173/50000000000000 : ℝ)^3513
        have hw : |(521803333/1000000000 : ℝ)|=(521803333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s7_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337785223/2500000000 : ℝ)*x 0 + (-982963943/5000000000 : ℝ)*x 1 + (521803357/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337785223/2500000000 : ℝ)^4537 ≤ (44595553710343/100000000000000 : ℝ)^3513 := by
    have hnat : (1337785223 : ℕ)^4537*100000000000000^3513 ≤ 44595553710343^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337785223 2500000000 44595553710343 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982963943/5000000000 : ℝ)^4537 ≤ (2447262031127/20000000000000 : ℝ)^3513 := by
    have hnat : (982963943 : ℕ)^4537*20000000000000^3513 ≤ 2447262031127^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982963943 5000000000 2447262031127 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521803357/1000000000 : ℝ)^4537 ≤ (5396017014323/12500000000000 : ℝ)^3513 := by
    have hnat : (521803357 : ℕ)^4537*12500000000000^3513 ≤ 5396017014323^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521803357 1000000000 5396017014323 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337785223/2500000000 : ℝ), (-982963943/5000000000 : ℝ), (521803357/1000000000 : ℝ)] ![(44595553710343/100000000000000 : ℝ), (2447262031127/20000000000000 : ℝ), (5396017014323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337785223/2500000000 : ℝ)|^4537 ≤ (44595553710343/100000000000000 : ℝ)^3513
        have hw : |(1337785223/2500000000 : ℝ)|=(1337785223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982963943/5000000000 : ℝ)|^4537 ≤ (2447262031127/20000000000000 : ℝ)^3513
        have hw : |(-982963943/5000000000 : ℝ)|=(982963943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521803357/1000000000 : ℝ)|^4537 ≤ (5396017014323/12500000000000 : ℝ)^3513
        have hw : |(521803357/1000000000 : ℝ)|=(521803357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s7_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675570443/5000000000 : ℝ)*x 0 + (1043606731/2000000000 : ℝ)*x 1 + (-1965927781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675570443/5000000000 : ℝ)^4537 ≤ (8919110729153/20000000000000 : ℝ)^3513 := by
    have hnat : (2675570443 : ℕ)^4537*20000000000000^3513 ≤ 8919110729153^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675570443 5000000000 8919110729153 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043606731/2000000000 : ℝ)^4537 ≤ (43168137022751/100000000000000 : ℝ)^3513 := by
    have hnat : (1043606731 : ℕ)^4537*100000000000000^3513 ≤ 43168137022751^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043606731 2000000000 43168137022751 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965927781/10000000000 : ℝ)^4537 ≤ (2447261862319/20000000000000 : ℝ)^3513 := by
    have hnat : (1965927781 : ℕ)^4537*20000000000000^3513 ≤ 2447261862319^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965927781 10000000000 2447261862319 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675570443/5000000000 : ℝ), (1043606731/2000000000 : ℝ), (-1965927781/10000000000 : ℝ)] ![(8919110729153/20000000000000 : ℝ), (43168137022751/100000000000000 : ℝ), (2447261862319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675570443/5000000000 : ℝ)|^4537 ≤ (8919110729153/20000000000000 : ℝ)^3513
        have hw : |(2675570443/5000000000 : ℝ)|=(2675570443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043606731/2000000000 : ℝ)|^4537 ≤ (43168137022751/100000000000000 : ℝ)^3513
        have hw : |(1043606731/2000000000 : ℝ)|=(1043606731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965927781/10000000000 : ℝ)|^4537 ≤ (2447261862319/20000000000000 : ℝ)^3513
        have hw : |(-1965927781/10000000000 : ℝ)|=(1965927781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s7_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266061523/10000000000 : ℝ)*x 0 + (805555257/2000000000 : ℝ)*x 1 + (4516134281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266061523/10000000000 : ℝ)^4537 ≤ (832001648511/2500000000000 : ℝ)^3513 := by
    have hnat : (4266061523 : ℕ)^4537*2500000000000^3513 ≤ 832001648511^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266061523 10000000000 832001648511 2500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805555257/2000000000 : ℝ)^4537 ≤ (30899135432109/100000000000000 : ℝ)^3513 := by
    have hnat : (805555257 : ℕ)^4537*100000000000000^3513 ≤ 30899135432109^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805555257 2000000000 30899135432109 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516134281/10000000000 : ℝ)^4537 ≤ (35820798619697/100000000000000 : ℝ)^3513 := by
    have hnat : (4516134281 : ℕ)^4537*100000000000000^3513 ≤ 35820798619697^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516134281 10000000000 35820798619697 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266061523/10000000000 : ℝ), (805555257/2000000000 : ℝ), (4516134281/10000000000 : ℝ)] ![(832001648511/2500000000000 : ℝ), (30899135432109/100000000000000 : ℝ), (35820798619697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266061523/10000000000 : ℝ)|^4537 ≤ (832001648511/2500000000000 : ℝ)^3513
        have hw : |(4266061523/10000000000 : ℝ)|=(4266061523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805555257/2000000000 : ℝ)|^4537 ≤ (30899135432109/100000000000000 : ℝ)^3513
        have hw : |(805555257/2000000000 : ℝ)|=(805555257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516134281/10000000000 : ℝ)|^4537 ≤ (35820798619697/100000000000000 : ℝ)^3513
        have hw : |(4516134281/10000000000 : ℝ)|=(4516134281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s7_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-928146621/5000000000 : ℝ)*x 0 + (2609568803/5000000000 : ℝ)*x 1 + (2715539213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928146621/5000000000 : ℝ)^4537 ≤ (2840568682961/25000000000000 : ℝ)^3513 := by
    have hnat : (928146621 : ℕ)^4537*25000000000000^3513 ≤ 2840568682961^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928146621 5000000000 2840568682961 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609568803/5000000000 : ℝ)^4537 ≤ (21589966178439/50000000000000 : ℝ)^3513 := by
    have hnat : (2609568803 : ℕ)^4537*50000000000000^3513 ≤ 21589966178439^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609568803 5000000000 21589966178439 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715539213/5000000000 : ℝ)^4537 ≤ (2272889644859/5000000000000 : ℝ)^3513 := by
    have hnat : (2715539213 : ℕ)^4537*5000000000000^3513 ≤ 2272889644859^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715539213 5000000000 2272889644859 5000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928146621/5000000000 : ℝ), (2609568803/5000000000 : ℝ), (2715539213/5000000000 : ℝ)] ![(2840568682961/25000000000000 : ℝ), (21589966178439/50000000000000 : ℝ), (2272889644859/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928146621/5000000000 : ℝ)|^4537 ≤ (2840568682961/25000000000000 : ℝ)^3513
        have hw : |(-928146621/5000000000 : ℝ)|=(928146621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609568803/5000000000 : ℝ)|^4537 ≤ (21589966178439/50000000000000 : ℝ)^3513
        have hw : |(2609568803/5000000000 : ℝ)|=(2609568803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715539213/5000000000 : ℝ)|^4537 ≤ (2272889644859/5000000000000 : ℝ)^3513
        have hw : |(2715539213/5000000000 : ℝ)|=(2715539213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s7_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533265823/1250000000 : ℝ)*x 0 + (564202091/1250000000 : ℝ)*x 1 + (4030312631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533265823/1250000000 : ℝ)^4537 ≤ (16640360717727/50000000000000 : ℝ)^3513 := by
    have hnat : (533265823 : ℕ)^4537*50000000000000^3513 ≤ 16640360717727^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533265823 1250000000 16640360717727 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564202091/1250000000 : ℝ)^4537 ≤ (2237188220449/6250000000000 : ℝ)^3513 := by
    have hnat : (564202091 : ℕ)^4537*6250000000000^3513 ≤ 2237188220449^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564202091 1250000000 2237188220449 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030312631/10000000000 : ℝ)^4537 ≤ (6184853404419/20000000000000 : ℝ)^3513 := by
    have hnat : (4030312631 : ℕ)^4537*20000000000000^3513 ≤ 6184853404419^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030312631 10000000000 6184853404419 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533265823/1250000000 : ℝ), (564202091/1250000000 : ℝ), (4030312631/10000000000 : ℝ)] ![(16640360717727/50000000000000 : ℝ), (2237188220449/6250000000000 : ℝ), (6184853404419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533265823/1250000000 : ℝ)|^4537 ≤ (16640360717727/50000000000000 : ℝ)^3513
        have hw : |(533265823/1250000000 : ℝ)|=(533265823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564202091/1250000000 : ℝ)|^4537 ≤ (2237188220449/6250000000000 : ℝ)^3513
        have hw : |(564202091/1250000000 : ℝ)|=(564202091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030312631/10000000000 : ℝ)|^4537 ≤ (6184853404419/20000000000000 : ℝ)^3513
        have hw : |(4030312631/10000000000 : ℝ)|=(4030312631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10947/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5473/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5473/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5473/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5473/50000 : ℝ) ^ (4535/1024 : ℝ) ≤ (2780417928139751/50000000000000000000 : ℝ) := by
    have hpowers : (5473/50000 : ℝ)^4535 ≤ (2780417928139751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5473 : ℕ)^4535*50000000000000000000^1024 ≤ 2780417928139751^1024*50000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5473 50000 2780417928139751 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5473/50000 : ℝ)) (X := (2780417928139751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (5165739208970941/20000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4535 ≤ (5165739208970941/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4535*20000000000000000000^1024 ≤ 5165739208970941^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 5165739208970941 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (5165739208970941/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002780417928139751/25000000000000000000 : ℝ) ≤ (10000251115800749/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25002780417928139751/25000000000000000000 : ℝ)^1024 ≤ (10000251115800749/10000000000000000 : ℝ)^4535 := by
      have hnat : (25002780417928139751 : ℕ)^1024*10000000000000000^4535 ≤ 10000251115800749^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002780417928139751 25000000000000000000 10000251115800749 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000251115800749/10000000000000000 : ℝ)) (X := (25002780417928139751/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031389531901134207/100000000000000000000 : ℝ) ≤ (5000354343723737/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (100031389531901134207/100000000000000000000 : ℝ)^1024 ≤ (5000354343723737/5000000000000000 : ℝ)^4535 := by
      have hnat : (100031389531901134207 : ℕ)^1024*5000000000000000^4535 ≤ 5000354343723737^4535*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031389531901134207 100000000000000000000 5000354343723737 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354343723737/5000000000000000 : ℝ)) (X := (100031389531901134207/100000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005165739208970941/10000000000000000000 : ℝ) ≤ (10001166259094199/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10005165739208970941/10000000000000000000 : ℝ)^1024 ≤ (10001166259094199/10000000000000000 : ℝ)^4535 := by
      have hnat : (10005165739208970941 : ℕ)^1024*10000000000000000^4535 ≤ 10001166259094199^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005165739208970941 10000000000000000000 10001166259094199 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001166259094199/10000000000000000 : ℝ)) (X := (10005165739208970941/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2780417928139751/50000000000000000000 : ℝ) ≤ ((3489317088761376501/3490000000000000000 : ℝ)+2*(18302865869/18148000000000 : ℝ)*(5473/50000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (3489317088761376501/3490000000000000000 : ℝ)+2*(18302865869/18148000000000 : ℝ)*(5473/50000 : ℝ)=(10000251115800749/10000000000000000 : ℝ) by norm_num, show 1+2*(2780417928139751/50000000000000000000 : ℝ)=(25002780417928139751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5165739208970941/20000000000000000000 : ℝ)+(2780417928139751/50000000000000000000 : ℝ) ≤ ((3489317088761376501/3490000000000000000 : ℝ)+(18302865869/18148000000000 : ℝ)*((15483/100000 : ℝ)+(5473/50000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (3489317088761376501/3490000000000000000 : ℝ)+(18302865869/18148000000000 : ℝ)*((15483/100000 : ℝ)+(5473/50000 : ℝ))=(5000354343723737/5000000000000000 : ℝ) by norm_num, show 1+(5165739208970941/20000000000000000000 : ℝ)+(2780417928139751/50000000000000000000 : ℝ)=(100031389531901134207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5165739208970941/20000000000000000000 : ℝ) ≤ ((3489317088761376501/3490000000000000000 : ℝ)+2*(18302865869/18148000000000 : ℝ)*(15483/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (3489317088761376501/3490000000000000000 : ℝ)+2*(18302865869/18148000000000 : ℝ)*(15483/100000 : ℝ)=(10001166259094199/10000000000000000 : ℝ) by norm_num, show 1+2*(5165739208970941/20000000000000000000 : ℝ)=(10005165739208970941/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3489317088761376501/3490000000000000000 : ℝ)*(X 1 0+X 2 0)+(18302865869/18148000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3489317088761376501/3490000000000000000 : ℝ)) (alpha := (18302865869/18148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3489317088761376501/3490000000000000000 : ℝ)*(X 0 1+X 2 1)+(18302865869/18148000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3489317088761376501/3490000000000000000 : ℝ)) (alpha := (18302865869/18148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3489317088761376501/3490000000000000000 : ℝ)*(X 0 2+X 1 2)+(18302865869/18148000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (5473/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3489317088761376501/3490000000000000000 : ℝ)) (alpha := (18302865869/18148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1856264767/10000000000 : ℝ)*X 0 0+(5432190721/10000000000 : ℝ)*X 0 1+(521803333/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337785223/2500000000 : ℝ)*X 1 0+(-982963943/5000000000 : ℝ)*X 1 1+(521803357/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675570443/5000000000 : ℝ)*X 2 0+(1043606731/2000000000 : ℝ)*X 2 1+(-1965927781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266061523/10000000000 : ℝ)*X 0 0+(805555257/2000000000 : ℝ)*X 0 1+(4516134281/10000000000 : ℝ)*X 0 2+(4266061523/10000000000 : ℝ)*X 1 0+(805555257/2000000000 : ℝ)*X 1 1+(4516134281/10000000000 : ℝ)*X 1 2+(4266061523/10000000000 : ℝ)*X 2 0+(805555257/2000000000 : ℝ)*X 2 1+(4516134281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-928146621/5000000000 : ℝ)*X 0 0+(2609568803/5000000000 : ℝ)*X 0 1+(2715539213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((533265823/1250000000 : ℝ)*X 0 0+(564202091/1250000000 : ℝ)*X 0 1+(4030312631/10000000000 : ℝ)*X 0 2+(533265823/1250000000 : ℝ)*X 1 0+(564202091/1250000000 : ℝ)*X 1 1+(4030312631/10000000000 : ℝ)*X 1 2+(533265823/1250000000 : ℝ)*X 2 0+(564202091/1250000000 : ℝ)*X 2 1+(4030312631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (605148145250926778402409171/283562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215931711/50000000000000 : ℝ)*(base19) + (19092009/5000000000000 : ℝ)*(base23) + (23966449/100000000000000 : ℝ)*(lower2) + (4172601/12500000000000 : ℝ)*(upper3) + (101519123/100000000000000 : ℝ)*(upper5) + (839646507637111/25000000000000 : ℝ)*(major0) + (839646507637111/25000000000000 : ℝ)*(major1) + (839646507637111/25000000000000 : ℝ)*(major2) + (18677894961021/400000000000 : ℝ)*(sp0) + (4669486695347309/100000000000000 : ℝ)*(sp1) + (4669486745370551/100000000000000 : ℝ)*(sp2) + (1023840894532553/50000000000000 : ℝ)*(sp3) + (13386955481/100000000000000 : ℝ)*(sp4) + (768421171/25000000000000 : ℝ)*(sp5) + (204768486274979/10000000000000 : ℝ)*(f.failure) + (4669487127210731/100000000000000 : ℝ)*(f.sum) + (6113396259863/2268500000000000000000000000 : ℝ)*base65 + (5610494063653071943/1134250000000000000000000000000000 : ℝ)*base67 + (9059726878596571943/1134250000000000000000000000000000 : ℝ)*base69 + (9179347462881071943/1134250000000000000000000000000000 : ℝ)*base71 + (1669094378353/567125000000000000000000000 : ℝ)*base73 + (7605473507649571943/1134250000000000000000000000000000 : ℝ)*base75 + (3117474740969571943/1134250000000000000000000000000000 : ℝ)*base77 + (1883994948035178057/1134250000000000000000000000000000 : ℝ)*base80 + (8433201216497/4537000000000000000000000000 : ℝ)*base81 + (717637/1000000000000000000000 : ℝ)*base90 + (717637/1000000000000000000000 : ℝ)*base92 + (717637/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1520_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_box_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1644057329/10000000000 : ℝ)*x 0 + (540196791/1000000000 : ℝ)*x 1 + (1080393589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1644057329/10000000000 : ℝ)^4537 ≤ (4856636183299/50000000000000 : ℝ)^3513 := by
    have hnat : (1644057329 : ℕ)^4537*50000000000000^3513 ≤ 4856636183299^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644057329 10000000000 4856636183299 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540196791/1000000000 : ℝ)^4537 ≤ (11285840905321/25000000000000 : ℝ)^3513 := by
    have hnat : (540196791 : ℕ)^4537*25000000000000^3513 ≤ 11285840905321^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540196791 1000000000 11285840905321 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080393589/2000000000 : ℝ)^4537 ≤ (45143363999031/100000000000000 : ℝ)^3513 := by
    have hnat : (1080393589 : ℕ)^4537*100000000000000^3513 ≤ 45143363999031^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080393589 2000000000 45143363999031 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1644057329/10000000000 : ℝ), (540196791/1000000000 : ℝ), (1080393589/2000000000 : ℝ)] ![(4856636183299/50000000000000 : ℝ), (11285840905321/25000000000000 : ℝ), (45143363999031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1644057329/10000000000 : ℝ)|^4537 ≤ (4856636183299/50000000000000 : ℝ)^3513
        have hw : |(-1644057329/10000000000 : ℝ)|=(1644057329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540196791/1000000000 : ℝ)|^4537 ≤ (11285840905321/25000000000000 : ℝ)^3513
        have hw : |(540196791/1000000000 : ℝ)|=(540196791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080393589/2000000000 : ℝ)|^4537 ≤ (45143363999031/100000000000000 : ℝ)^3513
        have hw : |(1080393589/2000000000 : ℝ)|=(1080393589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270873683/10000000000 : ℝ)*x 0 + (-1825965793/10000000000 : ℝ)*x 1 + (5401968179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270873683/10000000000 : ℝ)^4537 ≤ (34986822599/80000000000 : ℝ)^3513 := by
    have hnat : (5270873683 : ℕ)^4537*80000000000^3513 ≤ 34986822599^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270873683 10000000000 34986822599 80000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825965793/10000000000 : ℝ)^4537 ≤ (11123105204529/100000000000000 : ℝ)^3513 := by
    have hnat : (1825965793 : ℕ)^4537*100000000000000^3513 ≤ 11123105204529^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825965793 10000000000 11123105204529 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401968179/10000000000 : ℝ)^4537 ≤ (45143366524537/100000000000000 : ℝ)^3513 := by
    have hnat : (5401968179 : ℕ)^4537*100000000000000^3513 ≤ 45143366524537^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401968179 10000000000 45143366524537 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270873683/10000000000 : ℝ), (-1825965793/10000000000 : ℝ), (5401968179/10000000000 : ℝ)] ![(34986822599/80000000000 : ℝ), (11123105204529/100000000000000 : ℝ), (45143366524537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270873683/10000000000 : ℝ)|^4537 ≤ (34986822599/80000000000 : ℝ)^3513
        have hw : |(5270873683/10000000000 : ℝ)|=(5270873683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1825965793/10000000000 : ℝ)|^4537 ≤ (11123105204529/100000000000000 : ℝ)^3513
        have hw : |(-1825965793/10000000000 : ℝ)|=(1825965793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401968179/10000000000 : ℝ)|^4537 ≤ (45143366524537/100000000000000 : ℝ)^3513
        have hw : |(5401968179/10000000000 : ℝ)|=(5401968179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317718481/2500000000 : ℝ)*x 0 + (540196787/1000000000 : ℝ)*x 1 + (-1825965889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317718481/2500000000 : ℝ)^4537 ≤ (21866765415623/50000000000000 : ℝ)^3513 := by
    have hnat : (1317718481 : ℕ)^4537*50000000000000^3513 ≤ 21866765415623^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317718481 2500000000 21866765415623 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540196787/1000000000 : ℝ)^4537 ≤ (22571681594787/50000000000000 : ℝ)^3513 := by
    have hnat : (540196787 : ℕ)^4537*50000000000000^3513 ≤ 22571681594787^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540196787 1000000000 22571681594787 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1825965889/10000000000 : ℝ)^4537 ≤ (11123105959787/100000000000000 : ℝ)^3513 := by
    have hnat : (1825965889 : ℕ)^4537*100000000000000^3513 ≤ 11123105959787^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825965889 10000000000 11123105959787 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317718481/2500000000 : ℝ), (540196787/1000000000 : ℝ), (-1825965889/10000000000 : ℝ)] ![(21866765415623/50000000000000 : ℝ), (22571681594787/50000000000000 : ℝ), (11123105959787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317718481/2500000000 : ℝ)|^4537 ≤ (21866765415623/50000000000000 : ℝ)^3513
        have hw : |(1317718481/2500000000 : ℝ)|=(1317718481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540196787/1000000000 : ℝ)|^4537 ≤ (22571681594787/50000000000000 : ℝ)^3513
        have hw : |(540196787/1000000000 : ℝ)|=(540196787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1825965889/10000000000 : ℝ)|^4537 ≤ (11123105959787/100000000000000 : ℝ)^3513
        have hw : |(-1825965889/10000000000 : ℝ)|=(1825965889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4468764867/10000000000 : ℝ)*x 0 + (2085819983/5000000000 : ℝ)*x 1 + (521455027/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468764867/10000000000 : ℝ)^4537 ≤ (7067260346839/20000000000000 : ℝ)^3513 := by
    have hnat : (4468764867 : ℕ)^4537*20000000000000^3513 ≤ 7067260346839^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468764867 10000000000 7067260346839 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085819983/5000000000 : ℝ)^4537 ≤ (1293273914817/4000000000000 : ℝ)^3513 := by
    have hnat : (2085819983 : ℕ)^4537*4000000000000^3513 ≤ 1293273914817^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085819983 5000000000 1293273914817 4000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521455027/1250000000 : ℝ)^4537 ≤ (32331850372811/100000000000000 : ℝ)^3513 := by
    have hnat : (521455027 : ℕ)^4537*100000000000000^3513 ≤ 32331850372811^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521455027 1250000000 32331850372811 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468764867/10000000000 : ℝ), (2085819983/5000000000 : ℝ), (521455027/1250000000 : ℝ)] ![(7067260346839/20000000000000 : ℝ), (1293273914817/4000000000000 : ℝ), (32331850372811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468764867/10000000000 : ℝ)|^4537 ≤ (7067260346839/20000000000000 : ℝ)^3513
        have hw : |(4468764867/10000000000 : ℝ)|=(4468764867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085819983/5000000000 : ℝ)|^4537 ≤ (1293273914817/4000000000000 : ℝ)^3513
        have hw : |(2085819983/5000000000 : ℝ)|=(2085819983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521455027/1250000000 : ℝ)|^4537 ≤ (32331850372811/100000000000000 : ℝ)^3513
        have hw : |(521455027/1250000000 : ℝ)|=(521455027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073900617/10000000000 : ℝ)*x 0 + (5243877747/10000000000 : ℝ)*x 1 + (5243874857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073900617/10000000000 : ℝ)^4537 ≤ (655555268287/5000000000000 : ℝ)^3513 := by
    have hnat : (2073900617 : ℕ)^4537*5000000000000^3513 ≤ 655555268287^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073900617 10000000000 655555268287 5000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243877747/10000000000 : ℝ)^4537 ≤ (43444462770987/100000000000000 : ℝ)^3513 := by
    have hnat : (5243877747 : ℕ)^4537*100000000000000^3513 ≤ 43444462770987^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243877747 10000000000 43444462770987 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243874857/10000000000 : ℝ)^4537 ≤ (5430553981099/12500000000000 : ℝ)^3513 := by
    have hnat : (5243874857 : ℕ)^4537*12500000000000^3513 ≤ 5430553981099^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243874857 10000000000 5430553981099 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073900617/10000000000 : ℝ), (5243877747/10000000000 : ℝ), (5243874857/10000000000 : ℝ)] ![(655555268287/5000000000000 : ℝ), (43444462770987/100000000000000 : ℝ), (5430553981099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073900617/10000000000 : ℝ)|^4537 ≤ (655555268287/5000000000000 : ℝ)^3513
        have hw : |(-2073900617/10000000000 : ℝ)|=(2073900617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243877747/10000000000 : ℝ)|^4537 ≤ (43444462770987/100000000000000 : ℝ)^3513
        have hw : |(5243877747/10000000000 : ℝ)|=(5243877747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243874857/10000000000 : ℝ)|^4537 ≤ (5430553981099/12500000000000 : ℝ)^3513
        have hw : |(5243874857/10000000000 : ℝ)|=(5243874857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380871713/10000000000 : ℝ)*x 0 + (-378259301/2000000000 : ℝ)*x 1 + (2621938533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380871713/10000000000 : ℝ)^4537 ≤ (44915807129553/100000000000000 : ℝ)^3513 := by
    have hnat : (5380871713 : ℕ)^4537*100000000000000^3513 ≤ 44915807129553^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380871713 10000000000 44915807129553 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378259301/2000000000 : ℝ)^4537 ≤ (11639737369469/100000000000000 : ℝ)^3513 := by
    have hnat : (378259301 : ℕ)^4537*100000000000000^3513 ≤ 11639737369469^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378259301 2000000000 11639737369469 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621938533/5000000000 : ℝ)^4537 ≤ (10861113871119/25000000000000 : ℝ)^3513 := by
    have hnat : (2621938533 : ℕ)^4537*25000000000000^3513 ≤ 10861113871119^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621938533 5000000000 10861113871119 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380871713/10000000000 : ℝ), (-378259301/2000000000 : ℝ), (2621938533/5000000000 : ℝ)] ![(44915807129553/100000000000000 : ℝ), (11639737369469/100000000000000 : ℝ), (10861113871119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380871713/10000000000 : ℝ)|^4537 ≤ (44915807129553/100000000000000 : ℝ)^3513
        have hw : |(5380871713/10000000000 : ℝ)|=(5380871713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378259301/2000000000 : ℝ)|^4537 ≤ (11639737369469/100000000000000 : ℝ)^3513
        have hw : |(-378259301/2000000000 : ℝ)|=(378259301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621938533/5000000000 : ℝ)|^4537 ≤ (10861113871119/25000000000000 : ℝ)^3513
        have hw : |(2621938533/5000000000 : ℝ)|=(2621938533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380873429/10000000000 : ℝ)*x 0 + (1048775021/2000000000 : ℝ)*x 1 + (-945648409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380873429/10000000000 : ℝ)^4537 ≤ (44915825628819/100000000000000 : ℝ)^3513 := by
    have hnat : (5380873429 : ℕ)^4537*100000000000000^3513 ≤ 44915825628819^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380873429 10000000000 44915825628819 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048775021/2000000000 : ℝ)^4537 ≤ (43444434502323/100000000000000 : ℝ)^3513 := by
    have hnat : (1048775021 : ℕ)^4537*100000000000000^3513 ≤ 43444434502323^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048775021 2000000000 43444434502323 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945648409/5000000000 : ℝ)^4537 ≤ (11639739857287/100000000000000 : ℝ)^3513 := by
    have hnat : (945648409 : ℕ)^4537*100000000000000^3513 ≤ 11639739857287^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945648409 5000000000 11639739857287 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380873429/10000000000 : ℝ), (1048775021/2000000000 : ℝ), (-945648409/5000000000 : ℝ)] ![(44915825628819/100000000000000 : ℝ), (43444434502323/100000000000000 : ℝ), (11639739857287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380873429/10000000000 : ℝ)|^4537 ≤ (44915825628819/100000000000000 : ℝ)^3513
        have hw : |(5380873429/10000000000 : ℝ)|=(5380873429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048775021/2000000000 : ℝ)|^4537 ≤ (43444434502323/100000000000000 : ℝ)^3513
        have hw : |(1048775021/2000000000 : ℝ)|=(1048775021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945648409/5000000000 : ℝ)|^4537 ≤ (11639739857287/100000000000000 : ℝ)^3513
        have hw : |(-945648409/5000000000 : ℝ)|=(945648409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (812179961/2000000000 : ℝ)*x 0 + (2187719771/5000000000 : ℝ)*x 1 + (1093859793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812179961/2000000000 : ℝ)^4537 ≤ (15613852491173/50000000000000 : ℝ)^3513 := by
    have hnat : (812179961 : ℕ)^4537*50000000000000^3513 ≤ 15613852491173^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812179961 2000000000 15613852491173 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187719771/5000000000 : ℝ)^4537 ≤ (17193074690121/50000000000000 : ℝ)^3513 := by
    have hnat : (2187719771 : ℕ)^4537*50000000000000^3513 ≤ 17193074690121^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187719771 5000000000 17193074690121 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093859793/2500000000 : ℝ)^4537 ≤ (34386145624859/100000000000000 : ℝ)^3513 := by
    have hnat : (1093859793 : ℕ)^4537*100000000000000^3513 ≤ 34386145624859^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093859793 2500000000 34386145624859 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(812179961/2000000000 : ℝ), (2187719771/5000000000 : ℝ), (1093859793/2500000000 : ℝ)] ![(15613852491173/50000000000000 : ℝ), (17193074690121/50000000000000 : ℝ), (34386145624859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(812179961/2000000000 : ℝ)|^4537 ≤ (15613852491173/50000000000000 : ℝ)^3513
        have hw : |(812179961/2000000000 : ℝ)|=(812179961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2187719771/5000000000 : ℝ)|^4537 ≤ (17193074690121/50000000000000 : ℝ)^3513
        have hw : |(2187719771/5000000000 : ℝ)|=(2187719771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093859793/2500000000 : ℝ)|^4537 ≤ (34386145624859/100000000000000 : ℝ)^3513
        have hw : |(1093859793/2500000000 : ℝ)|=(1093859793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_8 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983022633/10000000000 : ℝ)*x 0 + (641629173/1250000000 : ℝ)*x 1 + (5422396817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983022633/10000000000 : ℝ)^4537 ≤ (12373899600501/100000000000000 : ℝ)^3513 := by
    have hnat : (1983022633 : ℕ)^4537*100000000000000^3513 ≤ 12373899600501^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983022633 10000000000 12373899600501 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641629173/1250000000 : ℝ)^4537 ≤ (8452426207309/20000000000000 : ℝ)^3513 := by
    have hnat : (641629173 : ℕ)^4537*20000000000000^3513 ≤ 8452426207309^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641629173 1250000000 8452426207309 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422396817/10000000000 : ℝ)^4537 ≤ (2835248083753/6250000000000 : ℝ)^3513 := by
    have hnat : (5422396817 : ℕ)^4537*6250000000000^3513 ≤ 2835248083753^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422396817 10000000000 2835248083753 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983022633/10000000000 : ℝ), (641629173/1250000000 : ℝ), (5422396817/10000000000 : ℝ)] ![(12373899600501/100000000000000 : ℝ), (8452426207309/20000000000000 : ℝ), (2835248083753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983022633/10000000000 : ℝ)|^4537 ≤ (12373899600501/100000000000000 : ℝ)^3513
        have hw : |(-1983022633/10000000000 : ℝ)|=(1983022633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641629173/1250000000 : ℝ)|^4537 ≤ (8452426207309/20000000000000 : ℝ)^3513
        have hw : |(641629173/1250000000 : ℝ)|=(641629173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422396817/10000000000 : ℝ)|^4537 ≤ (2835248083753/6250000000000 : ℝ)^3513
        have hw : |(5422396817/10000000000 : ℝ)|=(5422396817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_9 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628326927/5000000000 : ℝ)*x 0 + (-1817279779/10000000000 : ℝ)*x 1 + (2711198461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628326927/5000000000 : ℝ)^4537 ≤ (43581212079887/100000000000000 : ℝ)^3513 := by
    have hnat : (2628326927 : ℕ)^4537*100000000000000^3513 ≤ 43581212079887^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628326927 5000000000 43581212079887 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1817279779/10000000000 : ℝ)^4537 ≤ (11054817419997/100000000000000 : ℝ)^3513 := by
    have hnat : (1817279779 : ℕ)^4537*100000000000000^3513 ≤ 11054817419997^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817279779 10000000000 11054817419997 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711198461/5000000000 : ℝ)^4537 ≤ (5670496309317/12500000000000 : ℝ)^3513 := by
    have hnat : (2711198461 : ℕ)^4537*12500000000000^3513 ≤ 5670496309317^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711198461 5000000000 5670496309317 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628326927/5000000000 : ℝ), (-1817279779/10000000000 : ℝ), (2711198461/5000000000 : ℝ)] ![(43581212079887/100000000000000 : ℝ), (11054817419997/100000000000000 : ℝ), (5670496309317/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628326927/5000000000 : ℝ)|^4537 ≤ (43581212079887/100000000000000 : ℝ)^3513
        have hw : |(2628326927/5000000000 : ℝ)|=(2628326927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1817279779/10000000000 : ℝ)|^4537 ≤ (11054817419997/100000000000000 : ℝ)^3513
        have hw : |(-1817279779/10000000000 : ℝ)|=(1817279779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711198461/5000000000 : ℝ)|^4537 ≤ (5670496309317/12500000000000 : ℝ)^3513
        have hw : |(2711198461/5000000000 : ℝ)|=(2711198461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_10 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628326911/5000000000 : ℝ)*x 0 + (1084479377/2000000000 : ℝ)*x 1 + (-908639937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628326911/5000000000 : ℝ)^4537 ≤ (43581211737253/100000000000000 : ℝ)^3513 := by
    have hnat : (2628326911 : ℕ)^4537*100000000000000^3513 ≤ 43581211737253^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628326911 5000000000 43581211737253 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084479377/2000000000 : ℝ)^4537 ≤ (11340992518691/25000000000000 : ℝ)^3513 := by
    have hnat : (1084479377 : ℕ)^4537*25000000000000^3513 ≤ 11340992518691^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084479377 2000000000 11340992518691 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908639937/5000000000 : ℝ)^4537 ≤ (11054818166349/100000000000000 : ℝ)^3513 := by
    have hnat : (908639937 : ℕ)^4537*100000000000000^3513 ≤ 11054818166349^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908639937 5000000000 11054818166349 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628326911/5000000000 : ℝ), (1084479377/2000000000 : ℝ), (-908639937/5000000000 : ℝ)] ![(43581211737253/100000000000000 : ℝ), (11340992518691/25000000000000 : ℝ), (11054818166349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628326911/5000000000 : ℝ)|^4537 ≤ (43581211737253/100000000000000 : ℝ)^3513
        have hw : |(2628326911/5000000000 : ℝ)|=(2628326911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084479377/2000000000 : ℝ)|^4537 ≤ (11340992518691/25000000000000 : ℝ)^3513
        have hw : |(1084479377/2000000000 : ℝ)|=(1084479377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-908639937/5000000000 : ℝ)|^4537 ≤ (11054818166349/100000000000000 : ℝ)^3513
        have hw : |(-908639937/5000000000 : ℝ)|=(908639937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_11 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1130079833/2500000000 : ℝ)*x 0 + (4145272251/10000000000 : ℝ)*x 1 + (2072636119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1130079833/2500000000 : ℝ)^4537 ≤ (17931837516109/50000000000000 : ℝ)^3513 := by
    have hnat : (1130079833 : ℕ)^4537*50000000000000^3513 ≤ 17931837516109^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130079833 2500000000 17931837516109 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145272251/10000000000 : ℝ)^4537 ≤ (32068162537591/100000000000000 : ℝ)^3513 := by
    have hnat : (4145272251 : ℕ)^4537*100000000000000^3513 ≤ 32068162537591^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145272251 10000000000 32068162537591 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072636119/5000000000 : ℝ)^4537 ≤ (32068162407707/100000000000000 : ℝ)^3513 := by
    have hnat : (2072636119 : ℕ)^4537*100000000000000^3513 ≤ 32068162407707^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072636119 5000000000 32068162407707 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1130079833/2500000000 : ℝ), (4145272251/10000000000 : ℝ), (2072636119/5000000000 : ℝ)] ![(17931837516109/50000000000000 : ℝ), (32068162537591/100000000000000 : ℝ), (32068162407707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1130079833/2500000000 : ℝ)|^4537 ≤ (17931837516109/50000000000000 : ℝ)^3513
        have hw : |(1130079833/2500000000 : ℝ)|=(1130079833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145272251/10000000000 : ℝ)|^4537 ≤ (32068162537591/100000000000000 : ℝ)^3513
        have hw : |(4145272251/10000000000 : ℝ)|=(4145272251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072636119/5000000000 : ℝ)|^4537 ≤ (32068162407707/100000000000000 : ℝ)^3513
        have hw : |(2072636119/5000000000 : ℝ)|=(2072636119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_12 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1734842063/10000000000 : ℝ)*x 0 + (5509274907/10000000000 : ℝ)*x 1 + (2614421997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1734842063/10000000000 : ℝ)^4537 ≤ (5205743614857/50000000000000 : ℝ)^3513 := by
    have hnat : (1734842063 : ℕ)^4537*50000000000000^3513 ≤ 5205743614857^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734842063 10000000000 5205743614857 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509274907/10000000000 : ℝ)^4537 ≤ (46304839715217/100000000000000 : ℝ)^3513 := by
    have hnat : (5509274907 : ℕ)^4537*100000000000000^3513 ≤ 46304839715217^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509274907 10000000000 46304839715217 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614421997/5000000000 : ℝ)^4537 ≤ (21641836523841/50000000000000 : ℝ)^3513 := by
    have hnat : (2614421997 : ℕ)^4537*50000000000000^3513 ≤ 21641836523841^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614421997 5000000000 21641836523841 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1734842063/10000000000 : ℝ), (5509274907/10000000000 : ℝ), (2614421997/5000000000 : ℝ)] ![(5205743614857/50000000000000 : ℝ), (46304839715217/100000000000000 : ℝ), (21641836523841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1734842063/10000000000 : ℝ)|^4537 ≤ (5205743614857/50000000000000 : ℝ)^3513
        have hw : |(-1734842063/10000000000 : ℝ)|=(1734842063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509274907/10000000000 : ℝ)|^4537 ≤ (46304839715217/100000000000000 : ℝ)^3513
        have hw : |(5509274907/10000000000 : ℝ)|=(5509274907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614421997/5000000000 : ℝ)|^4537 ≤ (21641836523841/50000000000000 : ℝ)^3513
        have hw : |(2614421997/5000000000 : ℝ)|=(2614421997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_13 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347833071/2500000000 : ℝ)*x 0 + (-379466079/2000000000 : ℝ)*x 1 + (522884393/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347833071/2500000000 : ℝ)^4537 ≤ (180114435237/400000000000 : ℝ)^3513 := by
    have hnat : (1347833071 : ℕ)^4537*400000000000^3513 ≤ 180114435237^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347833071 2500000000 180114435237 400000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379466079/2000000000 : ℝ)^4537 ≤ (1460964851721/12500000000000 : ℝ)^3513 := by
    have hnat : (379466079 : ℕ)^4537*12500000000000^3513 ≤ 1460964851721^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379466079 2000000000 1460964851721 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522884393/1000000000 : ℝ)^4537 ≤ (2705229522717/6250000000000 : ℝ)^3513 := by
    have hnat : (522884393 : ℕ)^4537*6250000000000^3513 ≤ 2705229522717^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522884393 1000000000 2705229522717 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347833071/2500000000 : ℝ), (-379466079/2000000000 : ℝ), (522884393/1000000000 : ℝ)] ![(180114435237/400000000000 : ℝ), (1460964851721/12500000000000 : ℝ), (2705229522717/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347833071/2500000000 : ℝ)|^4537 ≤ (180114435237/400000000000 : ℝ)^3513
        have hw : |(1347833071/2500000000 : ℝ)|=(1347833071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379466079/2000000000 : ℝ)|^4537 ≤ (1460964851721/12500000000000 : ℝ)^3513
        have hw : |(-379466079/2000000000 : ℝ)|=(379466079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522884393/1000000000 : ℝ)|^4537 ≤ (2705229522717/6250000000000 : ℝ)^3513
        have hw : |(522884393/1000000000 : ℝ)|=(522884393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_14 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539133221/1000000000 : ℝ)*x 0 + (1307210989/2500000000 : ℝ)*x 1 + (-1897330461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539133221/1000000000 : ℝ)^4537 ≤ (11257152002761/25000000000000 : ℝ)^3513 := by
    have hnat : (539133221 : ℕ)^4537*25000000000000^3513 ≤ 11257152002761^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539133221 1000000000 11257152002761 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307210989/2500000000 : ℝ)^4537 ≤ (5410459080179/12500000000000 : ℝ)^3513 := by
    have hnat : (1307210989 : ℕ)^4537*12500000000000^3513 ≤ 5410459080179^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307210989 2500000000 5410459080179 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897330461/10000000000 : ℝ)^4537 ≤ (11687719338843/100000000000000 : ℝ)^3513 := by
    have hnat : (1897330461 : ℕ)^4537*100000000000000^3513 ≤ 11687719338843^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897330461 10000000000 11687719338843 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539133221/1000000000 : ℝ), (1307210989/2500000000 : ℝ), (-1897330461/10000000000 : ℝ)] ![(11257152002761/25000000000000 : ℝ), (5410459080179/12500000000000 : ℝ), (11687719338843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539133221/1000000000 : ℝ)|^4537 ≤ (11257152002761/25000000000000 : ℝ)^3513
        have hw : |(539133221/1000000000 : ℝ)|=(539133221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307210989/2500000000 : ℝ)|^4537 ≤ (5410459080179/12500000000000 : ℝ)^3513
        have hw : |(1307210989/2500000000 : ℝ)|=(1307210989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1897330461/10000000000 : ℝ)|^4537 ≤ (11687719338843/100000000000000 : ℝ)^3513
        have hw : |(-1897330461/10000000000 : ℝ)|=(1897330461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_box_15 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2010627869/5000000000 : ℝ)*x 0 + (1098698703/2500000000 : ℝ)*x 1 + (1098698733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010627869/5000000000 : ℝ)^4537 ≤ (15417273620201/50000000000000 : ℝ)^3513 := by
    have hnat : (2010627869 : ℕ)^4537*50000000000000^3513 ≤ 15417273620201^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010627869 5000000000 15417273620201 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098698703/2500000000 : ℝ)^4537 ≤ (8645681440473/25000000000000 : ℝ)^3513 := by
    have hnat : (1098698703 : ℕ)^4537*25000000000000^3513 ≤ 8645681440473^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098698703 2500000000 8645681440473 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098698733/2500000000 : ℝ)^4537 ≤ (17291363490711/50000000000000 : ℝ)^3513 := by
    have hnat : (1098698733 : ℕ)^4537*50000000000000^3513 ≤ 17291363490711^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098698733 2500000000 17291363490711 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2010627869/5000000000 : ℝ), (1098698703/2500000000 : ℝ), (1098698733/2500000000 : ℝ)] ![(15417273620201/50000000000000 : ℝ), (8645681440473/25000000000000 : ℝ), (17291363490711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2010627869/5000000000 : ℝ)|^4537 ≤ (15417273620201/50000000000000 : ℝ)^3513
        have hw : |(2010627869/5000000000 : ℝ)|=(2010627869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098698703/2500000000 : ℝ)|^4537 ≤ (8645681440473/25000000000000 : ℝ)^3513
        have hw : |(1098698703/2500000000 : ℝ)|=(1098698703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098698733/2500000000 : ℝ)|^4537 ≤ (17291363490711/50000000000000 : ℝ)^3513
        have hw : |(1098698733/2500000000 : ℝ)|=(1098698733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(51/80 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11733/20000 : ℝ) ∧ (16081/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86053/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10947/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (1112617220442469/20000000000000000000 : ℝ) := by
    have hpowers : (10947/100000 : ℝ)^4535 ≤ (1112617220442469/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10947 : ℕ)^4535*20000000000000000000^1024 ≤ 1112617220442469^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10947 100000 1112617220442469 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10947/100000 : ℝ)) (X := (1112617220442469/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (5165739208970941/20000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4535 ≤ (5165739208970941/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4535*20000000000000000000^1024 ≤ 5165739208970941^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 5165739208970941 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (5165739208970941/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001112617220442469/10000000000000000000 : ℝ) ≤ (5000125608706403/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10001112617220442469/10000000000000000000 : ℝ)^1024 ≤ (5000125608706403/5000000000000000 : ℝ)^4535 := by
      have hnat : (10001112617220442469 : ℕ)^1024*5000000000000000^4535 ≤ 5000125608706403^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001112617220442469 10000000000000000000 5000125608706403 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000125608706403/5000000000000000 : ℝ)) (X := (10001112617220442469/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000627835642941341/2000000000000000000 : ℝ) ≤ (5000354369122767/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (2000627835642941341/2000000000000000000 : ℝ)^1024 ≤ (5000354369122767/5000000000000000 : ℝ)^4535 := by
      have hnat : (2000627835642941341 : ℕ)^1024*5000000000000000^4535 ≤ 5000354369122767^4535*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000627835642941341 2000000000000000000 5000354369122767 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354369122767/5000000000000000 : ℝ)) (X := (2000627835642941341/2000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005165739208970941/10000000000000000000 : ℝ) ≤ (5000583129539131/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10005165739208970941/10000000000000000000 : ℝ)^1024 ≤ (5000583129539131/5000000000000000 : ℝ)^4535 := by
      have hnat : (10005165739208970941 : ℕ)^1024*5000000000000000^4535 ≤ 5000583129539131^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005165739208970941 10000000000000000000 5000583129539131 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000583129539131/5000000000000000 : ℝ)) (X := (10005165739208970941/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1112617220442469/20000000000000000000 : ℝ) ≤ ((236203763338920527/236250000000000000 : ℝ)+2*(57190104091/56700000000000 : ℝ)*(10947/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (236203763338920527/236250000000000000 : ℝ)+2*(57190104091/56700000000000 : ℝ)*(10947/100000 : ℝ)=(5000125608706403/5000000000000000 : ℝ) by norm_num, show 1+2*(1112617220442469/20000000000000000000 : ℝ)=(10001112617220442469/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5165739208970941/20000000000000000000 : ℝ)+(1112617220442469/20000000000000000000 : ℝ) ≤ ((236203763338920527/236250000000000000 : ℝ)+(57190104091/56700000000000 : ℝ)*((15483/100000 : ℝ)+(10947/100000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (236203763338920527/236250000000000000 : ℝ)+(57190104091/56700000000000 : ℝ)*((15483/100000 : ℝ)+(10947/100000 : ℝ))=(5000354369122767/5000000000000000 : ℝ) by norm_num, show 1+(5165739208970941/20000000000000000000 : ℝ)+(1112617220442469/20000000000000000000 : ℝ)=(2000627835642941341/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5165739208970941/20000000000000000000 : ℝ) ≤ ((236203763338920527/236250000000000000 : ℝ)+2*(57190104091/56700000000000 : ℝ)*(15483/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (236203763338920527/236250000000000000 : ℝ)+2*(57190104091/56700000000000 : ℝ)*(15483/100000 : ℝ)=(5000583129539131/5000000000000000 : ℝ) by norm_num, show 1+2*(5165739208970941/20000000000000000000 : ℝ)=(10005165739208970941/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (236203763338920527/236250000000000000 : ℝ)*(X 1 0+X 2 0)+(57190104091/56700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (236203763338920527/236250000000000000 : ℝ)) (alpha := (57190104091/56700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (236203763338920527/236250000000000000 : ℝ)*(X 0 1+X 2 1)+(57190104091/56700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (236203763338920527/236250000000000000 : ℝ)) (alpha := (57190104091/56700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (236203763338920527/236250000000000000 : ℝ)*(X 0 2+X 1 2)+(57190104091/56700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (236203763338920527/236250000000000000 : ℝ)) (alpha := (57190104091/56700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1644057329/10000000000 : ℝ)*X 0 0+(540196791/1000000000 : ℝ)*X 0 1+(1080393589/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270873683/10000000000 : ℝ)*X 1 0+(-1825965793/10000000000 : ℝ)*X 1 1+(5401968179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317718481/2500000000 : ℝ)*X 2 0+(540196787/1000000000 : ℝ)*X 2 1+(-1825965889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468764867/10000000000 : ℝ)*X 0 0+(2085819983/5000000000 : ℝ)*X 0 1+(521455027/1250000000 : ℝ)*X 0 2+(4468764867/10000000000 : ℝ)*X 1 0+(2085819983/5000000000 : ℝ)*X 1 1+(521455027/1250000000 : ℝ)*X 1 2+(4468764867/10000000000 : ℝ)*X 2 0+(2085819983/5000000000 : ℝ)*X 2 1+(521455027/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2073900617/10000000000 : ℝ)*X 0 0+(5243877747/10000000000 : ℝ)*X 0 1+(5243874857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380871713/10000000000 : ℝ)*X 1 0+(-378259301/2000000000 : ℝ)*X 1 1+(2621938533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380873429/10000000000 : ℝ)*X 2 0+(1048775021/2000000000 : ℝ)*X 2 1+(-945648409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((812179961/2000000000 : ℝ)*X 0 0+(2187719771/5000000000 : ℝ)*X 0 1+(1093859793/2500000000 : ℝ)*X 0 2+(812179961/2000000000 : ℝ)*X 1 0+(2187719771/5000000000 : ℝ)*X 1 1+(1093859793/2500000000 : ℝ)*X 1 2+(812179961/2000000000 : ℝ)*X 2 0+(2187719771/5000000000 : ℝ)*X 2 1+(1093859793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1983022633/10000000000 : ℝ)*X 0 0+(641629173/1250000000 : ℝ)*X 0 1+(5422396817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628326927/5000000000 : ℝ)*X 1 0+(-1817279779/10000000000 : ℝ)*X 1 1+(2711198461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628326911/5000000000 : ℝ)*X 2 0+(1084479377/2000000000 : ℝ)*X 2 1+(-908639937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1130079833/2500000000 : ℝ)*X 0 0+(4145272251/10000000000 : ℝ)*X 0 1+(2072636119/5000000000 : ℝ)*X 0 2+(1130079833/2500000000 : ℝ)*X 1 0+(4145272251/10000000000 : ℝ)*X 1 1+(2072636119/5000000000 : ℝ)*X 1 2+(1130079833/2500000000 : ℝ)*X 2 0+(4145272251/10000000000 : ℝ)*X 2 1+(2072636119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1734842063/10000000000 : ℝ)*X 0 0+(5509274907/10000000000 : ℝ)*X 0 1+(2614421997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1347833071/2500000000 : ℝ)*X 1 0+(-379466079/2000000000 : ℝ)*X 1 1+(522884393/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((539133221/1000000000 : ℝ)*X 2 0+(1307210989/2500000000 : ℝ)*X 2 1+(-1897330461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2010627869/5000000000 : ℝ)*X 0 0+(1098698703/2500000000 : ℝ)*X 0 1+(1098698733/2500000000 : ℝ)*X 0 2+(2010627869/5000000000 : ℝ)*X 1 0+(1098698703/2500000000 : ℝ)*X 1 1+(1098698733/2500000000 : ℝ)*X 1 2+(2010627869/5000000000 : ℝ)*X 2 0+(1098698703/2500000000 : ℝ)*X 2 1+(1098698733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-51/80 : ℝ) ≤ (-602413919580007961450513143/945000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190981503/100000000000000 : ℝ)*(upper1) + (26705171/50000000000000 : ℝ)*(upper4) + (65830907/20000000000000 : ℝ)*(upper5) + (2235235808026217/100000000000000 : ℝ)*(major0) + (2235235808026217/100000000000000 : ℝ)*(major1) + (2235235808026217/100000000000000 : ℝ)*(major2) + (40567462937/100000000000000 : ℝ)*(sp2) + (612562483/6250000000000 : ℝ)*(sp3) + (1564440536717019/50000000000000 : ℝ)*(sp4) + (3128891855200109/100000000000000 : ℝ)*(sp5) + (782221730035891/25000000000000 : ℝ)*(sp6) + (272556699137071/20000000000000 : ℝ)*(sp7) + (46414172463/100000000000000 : ℝ)*(sp8) + (4454050799/12500000000000 : ℝ)*(sp13) + (1362793296685083/100000000000000 : ℝ)*(f.failure) + (3128927487606501/100000000000000 : ℝ)*(f.sum) + (6862824178963/2835000000000000000000000000 : ℝ)*base66 + (86496889545470489/10125000000000000000000000000000 : ℝ)*base68 + (21733019075904511/10125000000000000000000000000000 : ℝ)*base69 + (74435930415470489/10125000000000000000000000000000 : ℝ)*base72 + (2682141489427/708750000000000000000000000 : ℝ)*base74 + (32346368916279511/10125000000000000000000000000000 : ℝ)*base75 + (30939605132154511/10125000000000000000000000000000 : ℝ)*base77 + (18885695769470489/10125000000000000000000000000000 : ℝ)*base80 + (2180475319321/1417500000000000000000000000 : ℝ)*base81 + (32996851/10000000000000000000000 : ℝ)*base89 + (32996851/10000000000000000000000 : ℝ)*base91 + (32996851/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11733/20000 : ℝ) ≤ (2310046084227450481133025731653/3937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19897159/100000000000000 : ℝ)*(lower1) + (14659743/50000000000000 : ℝ)*(lower3) + (8151/625000000000 : ℝ)*(upper5) + (2312009224329387/100000000000000 : ℝ)*(major0) + (2312009224329387/100000000000000 : ℝ)*(major1) + (2312009224329387/100000000000000 : ℝ)*(major2) + (399357630277997/12500000000000 : ℝ)*(sp0) + (399356959414091/12500000000000 : ℝ)*(sp1) + (1597426134931087/50000000000000 : ℝ)*(sp2) + (704800317580223/50000000000000 : ℝ)*(sp3) + (5808618691/100000000000000 : ℝ)*(sp5) + (599813/156250000000 : ℝ)*(sp7) + (1842813849/20000000000000 : ℝ)*(sp10) + (441707443/100000000000000 : ℝ)*(sp12) + (704800509520383/50000000000000 : ℝ)*(f.failure) + (1597430741965709/50000000000000 : ℝ)*(f.sum) + (1650432300767/472500000000000000000000000 : ℝ)*base65 + (6994127585534207/3375000000000000000000000000000 : ℝ)*base67 + (8814444632159207/3375000000000000000000000000000 : ℝ)*base69 + (7489672247534207/3375000000000000000000000000000 : ℝ)*base71 + (212701387337/472500000000000000000000000 : ℝ)*base73 + (5083631018159207/3375000000000000000000000000000 : ℝ)*base75 + (7161182623409207/3375000000000000000000000000000 : ℝ)*base77 + (6322474762034207/3375000000000000000000000000000 : ℝ)*base79 + (2210791473461/945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (35399049/5000000000000000000000 : ℝ)*base90 + (35399049/5000000000000000000000 : ℝ)*base92 + (35399049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16081/20000 : ℝ) ≤ (316603941542418725652119028013/393750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (862893/10000000000000 : ℝ)*(upper1) + (1443033/5000000000000 : ℝ)*(upper2) + (306247/2000000000000 : ℝ)*(lower5) + (500990015219019/20000000000000 : ℝ)*(major0) + (500990015219019/20000000000000 : ℝ)*(major1) + (500990015219019/20000000000000 : ℝ)*(major2) + (8286081671/20000000000000 : ℝ)*(sp1) + (28910787209/100000000000000 : ℝ)*(sp2) + (10185414003/100000000000000 : ℝ)*(sp3) + (8900109/400000000000 : ℝ)*(sp4) + (1727930504071159/50000000000000 : ℝ)*(sp8) + (1727910901380607/50000000000000 : ℝ)*(sp9) + (86395858059559/2500000000000 : ℝ)*(sp10) + (763612141764473/50000000000000 : ℝ)*(sp11) + (30544689378859/2000000000000 : ℝ)*(f.failure) + (107995726036549/3125000000000 : ℝ)*(f.sum) + (30491598931/94500000000000000000000000 : ℝ)*base65 + (2586257532915641/675000000000000000000000000000 : ℝ)*base68 + (2914364956034359/675000000000000000000000000000 : ℝ)*base69 + (4805377872315641/675000000000000000000000000000 : ℝ)*base72 + (71231899499/47250000000000000000000000 : ℝ)*base73 + (1108138106940641/675000000000000000000000000000 : ℝ)*base76 + (3011617897440641/675000000000000000000000000000 : ℝ)*base78 + (701099691315641/675000000000000000000000000000 : ℝ)*base80 + (111177983537/47250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2526723/200000000000000000000 : ℝ)*base89 + (2526723/200000000000000000000 : ℝ)*base91 + (2526723/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-86053/100000 : ℝ) ≤ (-3388241788288373023782561303143/3937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9086579/100000000000000 : ℝ)*(lower0) + (2563513/20000000000000 : ℝ)*(lower3) + (10346561/25000000000000 : ℝ)*(lower4) + (2544216705543291/100000000000000 : ℝ)*(major0) + (2544216705543291/100000000000000 : ℝ)*(major1) + (2544216705543291/100000000000000 : ℝ)*(major2) + (568533841/50000000000000 : ℝ)*(sp4) + (7791837473/100000000000000 : ℝ)*(sp5) + (22133534929/100000000000000 : ℝ)*(sp6) + (3956302123/20000000000000 : ℝ)*(sp7) + (1782970498025073/50000000000000 : ℝ)*(sp12) + (713186868256071/20000000000000 : ℝ)*(sp13) + (3565919999582899/100000000000000 : ℝ)*(sp14) + (1551155024824599/100000000000000 : ℝ)*(sp15) + (775587403167607/50000000000000 : ℝ)*(f.failure) + (891485533279457/25000000000000 : ℝ)*(f.sum) + (273835389599/472500000000000000000000000 : ℝ)*base66 + (13677448992374551/3375000000000000000000000000000 : ℝ)*base67 + (15884716183125449/3375000000000000000000000000000 : ℝ)*base70 + (14063476948125449/3375000000000000000000000000000 : ℝ)*base72 + (987585745633/945000000000000000000000000 : ℝ)*base74 + (6948036031875449/3375000000000000000000000000000 : ℝ)*base76 + (2851039332375449/3375000000000000000000000000000 : ℝ)*base78 + (703975610999551/3375000000000000000000000000000 : ℝ)*base79 + (462806270347/236250000000000000000000000 : ℝ)*base82 + (22748079/5000000000000000000000 : ℝ)*base89 + (22748079/5000000000000000000000 : ℝ)*base91 + (22748079/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1520_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(51/80 : ℝ) ≤ X j i ∧ X j i ≤ -(11733/20000 : ℝ) else (16081/20000 : ℝ) ≤ X j i ∧ X j i ≤ (86053/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1520_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1520_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(51/80 : ℝ) ≤ X j i ∧ X j i ≤ -(11733/20000 : ℝ) else (16081/20000 : ℝ) ≤ X j i ∧ X j i ≤ (86053/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1520_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1520_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1520_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(51/80 : ℝ) ≤ X j i ∧ X j i ≤ -(11733/20000 : ℝ) else (16081/20000 : ℝ) ≤ X j i ∧ X j i ≤ (86053/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
