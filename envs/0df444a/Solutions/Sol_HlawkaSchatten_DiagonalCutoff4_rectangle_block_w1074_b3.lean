-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:56.513775+00:00
-- url     : https://prove2.me/submissions/2aac95fe-6dbe-44b5-82ac-d44d7fa1707c

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
theorem support_rectangle_w1074_s9_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099917701/5000000000 : ℝ)*x 0 + (5394188599/10000000000 : ℝ)*x 1 + (5264627537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099917701/5000000000 : ℝ)^8267 ≤ (13360738597071/100000000000000 : ℝ)^6219 := by
    have hnat : (1099917701 : ℕ)^8267*100000000000000^6219 ≤ 13360738597071^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099917701 5000000000 13360738597071 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394188599/10000000000 : ℝ)^8267 ≤ (8803914278673/20000000000000 : ℝ)^6219 := by
    have hnat : (5394188599 : ℕ)^8267*20000000000000^6219 ≤ 8803914278673^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394188599 10000000000 8803914278673 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264627537/10000000000 : ℝ)^8267 ≤ (42619689992677/100000000000000 : ℝ)^6219 := by
    have hnat : (5264627537 : ℕ)^8267*100000000000000^6219 ≤ 42619689992677^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264627537 10000000000 42619689992677 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099917701/5000000000 : ℝ), (5394188599/10000000000 : ℝ), (5264627537/10000000000 : ℝ)] ![(13360738597071/100000000000000 : ℝ), (8803914278673/20000000000000 : ℝ), (42619689992677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099917701/5000000000 : ℝ)|^8267 ≤ (13360738597071/100000000000000 : ℝ)^6219
        have hw : |(-1099917701/5000000000 : ℝ)|=(1099917701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394188599/10000000000 : ℝ)|^8267 ≤ (8803914278673/20000000000000 : ℝ)^6219
        have hw : |(5394188599/10000000000 : ℝ)|=(5394188599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264627537/10000000000 : ℝ)|^8267 ≤ (42619689992677/100000000000000 : ℝ)^6219
        have hw : |(5264627537/10000000000 : ℝ)|=(5264627537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s9_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099920091/5000000000 : ℝ)*x 0 + (2632476051/5000000000 : ℝ)*x 1 + (5393863059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099920091/5000000000 : ℝ)^8267 ≤ (13360777188931/100000000000000 : ℝ)^6219 := by
    have hnat : (1099920091 : ℕ)^8267*100000000000000^6219 ≤ 13360777188931^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099920091 5000000000 13360777188931 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632476051/5000000000 : ℝ)^8267 ≤ (42623182811911/100000000000000 : ℝ)^6219 := by
    have hnat : (2632476051 : ℕ)^8267*100000000000000^6219 ≤ 42623182811911^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632476051 5000000000 42623182811911 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393863059/10000000000 : ℝ)^8267 ≤ (44016039991783/100000000000000 : ℝ)^6219 := by
    have hnat : (5393863059 : ℕ)^8267*100000000000000^6219 ≤ 44016039991783^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393863059 10000000000 44016039991783 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099920091/5000000000 : ℝ), (2632476051/5000000000 : ℝ), (5393863059/10000000000 : ℝ)] ![(13360777188931/100000000000000 : ℝ), (42623182811911/100000000000000 : ℝ), (44016039991783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099920091/5000000000 : ℝ)|^8267 ≤ (13360777188931/100000000000000 : ℝ)^6219
        have hw : |(-1099920091/5000000000 : ℝ)|=(1099920091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632476051/5000000000 : ℝ)|^8267 ≤ (42623182811911/100000000000000 : ℝ)^6219
        have hw : |(2632476051/5000000000 : ℝ)|=(2632476051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393863059/10000000000 : ℝ)|^8267 ≤ (44016039991783/100000000000000 : ℝ)^6219
        have hw : |(5393863059/10000000000 : ℝ)|=(5393863059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s9_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132807493/250000000 : ℝ)*x 0 + (-33380191/156250000 : ℝ)*x 1 + (5393862509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132807493/250000000 : ℝ)^8267 ≤ (21566737129861/50000000000000 : ℝ)^6219 := by
    have hnat : (132807493 : ℕ)^8267*50000000000000^6219 ≤ 21566737129861^6219*250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132807493 250000000 21566737129861 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33380191/156250000 : ℝ)^8267 ≤ (1606311463167/12500000000000 : ℝ)^6219 := by
    have hnat : (33380191 : ℕ)^8267*12500000000000^6219 ≤ 1606311463167^6219*156250000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33380191 156250000 1606311463167 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393862509/10000000000 : ℝ)^8267 ≤ (22008017012769/50000000000000 : ℝ)^6219 := by
    have hnat : (5393862509 : ℕ)^8267*50000000000000^6219 ≤ 22008017012769^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393862509 10000000000 22008017012769 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132807493/250000000 : ℝ), (-33380191/156250000 : ℝ), (5393862509/10000000000 : ℝ)] ![(21566737129861/50000000000000 : ℝ), (1606311463167/12500000000000 : ℝ), (22008017012769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132807493/250000000 : ℝ)|^8267 ≤ (21566737129861/50000000000000 : ℝ)^6219
        have hw : |(132807493/250000000 : ℝ)|=(132807493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33380191/156250000 : ℝ)|^8267 ≤ (1606311463167/12500000000000 : ℝ)^6219
        have hw : |(-33380191/156250000 : ℝ)|=(33380191/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393862509/10000000000 : ℝ)|^8267 ≤ (22008017012769/50000000000000 : ℝ)^6219
        have hw : |(5393862509/10000000000 : ℝ)|=(5393862509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s9_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106245977/200000000 : ℝ)*x 0 + (5393863049/10000000000 : ℝ)*x 1 + (-427266533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106245977/200000000 : ℝ)^8267 ≤ (43133464869443/100000000000000 : ℝ)^6219 := by
    have hnat : (106245977 : ℕ)^8267*100000000000000^6219 ≤ 43133464869443^6219*200000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106245977 200000000 43133464869443 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393863049/10000000000 : ℝ)^8267 ≤ (22008019941653/50000000000000 : ℝ)^6219 := by
    have hnat : (5393863049 : ℕ)^8267*50000000000000^6219 ≤ 22008019941653^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393863049 10000000000 22008019941653 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427266533/2000000000 : ℝ)^8267 ≤ (12850495231617/100000000000000 : ℝ)^6219 := by
    have hnat : (427266533 : ℕ)^8267*100000000000000^6219 ≤ 12850495231617^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427266533 2000000000 12850495231617 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106245977/200000000 : ℝ), (5393863049/10000000000 : ℝ), (-427266533/2000000000 : ℝ)] ![(43133464869443/100000000000000 : ℝ), (22008019941653/50000000000000 : ℝ), (12850495231617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106245977/200000000 : ℝ)|^8267 ≤ (43133464869443/100000000000000 : ℝ)^6219
        have hw : |(106245977/200000000 : ℝ)|=(106245977/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393863049/10000000000 : ℝ)|^8267 ≤ (22008019941653/50000000000000 : ℝ)^6219
        have hw : |(5393863049/10000000000 : ℝ)|=(5393863049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427266533/2000000000 : ℝ)|^8267 ≤ (12850495231617/100000000000000 : ℝ)^6219
        have hw : |(-427266533/2000000000 : ℝ)|=(427266533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s9_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374355243/10000000000 : ℝ)*x 0 + (2251369281/5000000000 : ℝ)*x 1 + (4249689507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374355243/10000000000 : ℝ)^8267 ≤ (666334395539/2000000000000 : ℝ)^6219 := by
    have hnat : (4374355243 : ℕ)^8267*2000000000000^6219 ≤ 666334395539^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374355243 10000000000 666334395539 2000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251369281/5000000000 : ℝ)^8267 ≤ (69245566663/200000000000 : ℝ)^6219 := by
    have hnat : (2251369281 : ℕ)^8267*200000000000^6219 ≤ 69245566663^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251369281 5000000000 69245566663 200000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249689507/10000000000 : ℝ)^8267 ≤ (32060496873281/100000000000000 : ℝ)^6219 := by
    have hnat : (4249689507 : ℕ)^8267*100000000000000^6219 ≤ 32060496873281^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249689507 10000000000 32060496873281 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374355243/10000000000 : ℝ), (2251369281/5000000000 : ℝ), (4249689507/10000000000 : ℝ)] ![(666334395539/2000000000000 : ℝ), (69245566663/200000000000 : ℝ), (32060496873281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374355243/10000000000 : ℝ)|^8267 ≤ (666334395539/2000000000000 : ℝ)^6219
        have hw : |(4374355243/10000000000 : ℝ)|=(4374355243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251369281/5000000000 : ℝ)|^8267 ≤ (69245566663/200000000000 : ℝ)^6219
        have hw : |(2251369281/5000000000 : ℝ)|=(2251369281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249689507/10000000000 : ℝ)|^8267 ≤ (32060496873281/100000000000000 : ℝ)^6219
        have hw : |(4249689507/10000000000 : ℝ)|=(4249689507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s9_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-67520911/10000000000 : ℝ)*x 0 + (1165493969/2000000000 : ℝ)*x 1 + (6033697943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67520911/10000000000 : ℝ)^8267 ≤ (813810459/625000000000 : ℝ)^6219 := by
    have hnat : (67520911 : ℕ)^8267*625000000000^6219 ≤ 813810459^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67520911 10000000000 813810459 625000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165493969/2000000000 : ℝ)^8267 ≤ (48780861854621/100000000000000 : ℝ)^6219 := by
    have hnat : (1165493969 : ℕ)^8267*100000000000000^6219 ≤ 48780861854621^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165493969 2000000000 48780861854621 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033697943/10000000000 : ℝ)^8267 ≤ (10217785690859/20000000000000 : ℝ)^6219 := by
    have hnat : (6033697943 : ℕ)^8267*20000000000000^6219 ≤ 10217785690859^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033697943 10000000000 10217785690859 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67520911/10000000000 : ℝ), (1165493969/2000000000 : ℝ), (6033697943/10000000000 : ℝ)] ![(813810459/625000000000 : ℝ), (48780861854621/100000000000000 : ℝ), (10217785690859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67520911/10000000000 : ℝ)|^8267 ≤ (813810459/625000000000 : ℝ)^6219
        have hw : |(-67520911/10000000000 : ℝ)|=(67520911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165493969/2000000000 : ℝ)|^8267 ≤ (48780861854621/100000000000000 : ℝ)^6219
        have hw : |(1165493969/2000000000 : ℝ)|=(1165493969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033697943/10000000000 : ℝ)|^8267 ≤ (10217785690859/20000000000000 : ℝ)^6219
        have hw : |(6033697943/10000000000 : ℝ)|=(6033697943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1751/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1751/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (1487133412319131/10000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^4133 ≤ (1487133412319131/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^4133*10000000000000000000^1024 ≤ 1487133412319131^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 1487133412319131 10000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (1487133412319131/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1751/12500 : ℝ) ^ (4133/1024 : ℝ) ≤ (8966040780421393/25000000000000000000 : ℝ) := by
    have hpowers : (1751/12500 : ℝ)^4133 ≤ (8966040780421393/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1751 : ℕ)^4133*25000000000000000000^1024 ≤ 8966040780421393^1024*12500^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1751 12500 8966040780421393 25000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1751/12500 : ℝ)) (X := (8966040780421393/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001487133412319131/5000000000000000000 : ℝ) ≤ (2000147365525159/2000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (5001487133412319131/5000000000000000000 : ℝ)^1024 ≤ (2000147365525159/2000000000000000 : ℝ)^4133 := by
      have hnat : (5001487133412319131 : ℕ)^1024*2000000000000000^4133 ≤ 2000147365525159^4133*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001487133412319131 5000000000000000000 2000147365525159 2000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147365525159/2000000000000000 : ℝ)) (X := (5001487133412319131/5000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025367748622438441/50000000000000000000 : ℝ) ≤ (10001256792598861/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50025367748622438441/50000000000000000000 : ℝ)^1024 ≤ (10001256792598861/10000000000000000 : ℝ)^4133 := by
      have hnat : (50025367748622438441 : ℕ)^1024*10000000000000000^4133 ≤ 10001256792598861^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025367748622438441 50000000000000000000 10001256792598861 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001256792598861/10000000000000000 : ℝ)) (X := (50025367748622438441/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508966040780421393/12500000000000000000 : ℝ) ≤ (10001776757571927/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (12508966040780421393/12500000000000000000 : ℝ)^1024 ≤ (10001776757571927/10000000000000000 : ℝ)^4133 := by
      have hnat : (12508966040780421393 : ℕ)^1024*10000000000000000^4133 ≤ 10001776757571927^4133*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508966040780421393 12500000000000000000 10001776757571927 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001776757571927/10000000000000000 : ℝ)) (X := (12508966040780421393/12500000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1487133412319131/10000000000000000000 : ℝ) ≤ ((27440309860849522559/27450000000000000000 : ℝ)+2*(259982486533/137250000000000 : ℝ)*(11263/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (27440309860849522559/27450000000000000000 : ℝ)+2*(259982486533/137250000000000 : ℝ)*(11263/100000 : ℝ)=(2000147365525159/2000000000000000 : ℝ) by norm_num, show 1+2*(1487133412319131/10000000000000000000 : ℝ)=(5001487133412319131/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8966040780421393/25000000000000000000 : ℝ)+(1487133412319131/10000000000000000000 : ℝ) ≤ ((27440309860849522559/27450000000000000000 : ℝ)+(259982486533/137250000000000 : ℝ)*((1751/12500 : ℝ)+(11263/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (27440309860849522559/27450000000000000000 : ℝ)+(259982486533/137250000000000 : ℝ)*((1751/12500 : ℝ)+(11263/100000 : ℝ))=(10001256792598861/10000000000000000 : ℝ) by norm_num, show 1+(8966040780421393/25000000000000000000 : ℝ)+(1487133412319131/10000000000000000000 : ℝ)=(50025367748622438441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8966040780421393/25000000000000000000 : ℝ) ≤ ((27440309860849522559/27450000000000000000 : ℝ)+2*(259982486533/137250000000000 : ℝ)*(1751/12500 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (27440309860849522559/27450000000000000000 : ℝ)+2*(259982486533/137250000000000 : ℝ)*(1751/12500 : ℝ)=(10001776757571927/10000000000000000 : ℝ) by norm_num, show 1+2*(8966040780421393/25000000000000000000 : ℝ)=(12508966040780421393/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27440309860849522559/27450000000000000000 : ℝ)*(X 1 0+X 2 0)+(259982486533/137250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (27440309860849522559/27450000000000000000 : ℝ)) (alpha := (259982486533/137250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27440309860849522559/27450000000000000000 : ℝ)*(X 0 1+X 2 1)+(259982486533/137250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (27440309860849522559/27450000000000000000 : ℝ)) (alpha := (259982486533/137250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27440309860849522559/27450000000000000000 : ℝ)*(X 0 2+X 1 2)+(259982486533/137250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (1751/12500 : ℝ)) (c := (27440309860849522559/27450000000000000000 : ℝ)) (alpha := (259982486533/137250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1099917701/5000000000 : ℝ)*X 0 0+(5394188599/10000000000 : ℝ)*X 0 1+(5264627537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1099920091/5000000000 : ℝ)*X 0 0+(2632476051/5000000000 : ℝ)*X 0 1+(5393863059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132807493/250000000 : ℝ)*X 1 0+(-33380191/156250000 : ℝ)*X 1 1+(5393862509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((106245977/200000000 : ℝ)*X 2 0+(5393863049/10000000000 : ℝ)*X 2 1+(-427266533/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4374355243/10000000000 : ℝ)*X 0 0+(2251369281/5000000000 : ℝ)*X 0 1+(4249689507/10000000000 : ℝ)*X 0 2+(4374355243/10000000000 : ℝ)*X 1 0+(2251369281/5000000000 : ℝ)*X 1 1+(4249689507/10000000000 : ℝ)*X 1 2+(4374355243/10000000000 : ℝ)*X 2 0+(2251369281/5000000000 : ℝ)*X 2 1+(4249689507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((-67520911/10000000000 : ℝ)*X 0 0+(1165493969/2000000000 : ℝ)*X 0 1+(6033697943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s9_5 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42880455409890120200170199/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (543853591/100000000000000 : ℝ)*(upper1) + (197351281/50000000000000 : ℝ)*(lower2) + (16917943/10000000000000 : ℝ)*(lower3) + (1069587757/100000000000000 : ℝ)*(lower4) + (84147419/50000000000000 : ℝ)*(lower5) + (1170911217900117/20000000000000 : ℝ)*(major0) + (1170911217900117/20000000000000 : ℝ)*(major1) + (1170911217900117/20000000000000 : ℝ)*(major2) + (215902487/25000000000000 : ℝ)*(sp0) + (969661961421799/12500000000000 : ℝ)*(sp1) + (7757301205283497/100000000000000 : ℝ)*(sp2) + (7757301205283497/100000000000000 : ℝ)*(sp3) + (1975905439994939/50000000000000 : ℝ)*(sp4) + (1162574789/25000000000000 : ℝ)*(sp5) + (1975905439994939/50000000000000 : ℝ)*(f.failure) + (7757301205283497/100000000000000 : ℝ)*(f.sum) + (18381858579851/228750000000000000000000000 : ℝ)*base65 + (65125813121479801/183000000000000000000000000000000 : ℝ)*base67 + (3780814842143479801/183000000000000000000000000000000 : ℝ)*base69 + (282096084455479801/183000000000000000000000000000000 : ℝ)*base71 + (886389965377/457500000000000000000000000 : ℝ)*base73 + (1241222339180479801/183000000000000000000000000000000 : ℝ)*base75 + (18325281641825479801/183000000000000000000000000000000 : ℝ)*base77 + (2186670282429520199/183000000000000000000000000000000 : ℝ)*base80 + (462030963059/915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9474849/5000000000000000000000 : ℝ)*base89 + (9474849/5000000000000000000000 : ℝ)*base91 + (9474849/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1074_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_box_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070659029/10000000000 : ℝ)*x 0 + (5377256103/10000000000 : ℝ)*x 1 + (5377255523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070659029/10000000000 : ℝ)^8267 ≤ (2465607739337/20000000000000 : ℝ)^6219 := by
    have hnat : (2070659029 : ℕ)^8267*20000000000000^6219 ≤ 2465607739337^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070659029 10000000000 2465607739337 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377256103/10000000000 : ℝ)^8267 ≤ (43835983787053/100000000000000 : ℝ)^6219 := by
    have hnat : (5377256103 : ℕ)^8267*100000000000000^6219 ≤ 43835983787053^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377256103 10000000000 43835983787053 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377255523/10000000000 : ℝ)^8267 ≤ (21917988750881/50000000000000 : ℝ)^6219 := by
    have hnat : (5377255523 : ℕ)^8267*50000000000000^6219 ≤ 21917988750881^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377255523 10000000000 21917988750881 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070659029/10000000000 : ℝ), (5377256103/10000000000 : ℝ), (5377255523/10000000000 : ℝ)] ![(2465607739337/20000000000000 : ℝ), (43835983787053/100000000000000 : ℝ), (21917988750881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070659029/10000000000 : ℝ)|^8267 ≤ (2465607739337/20000000000000 : ℝ)^6219
        have hw : |(-2070659029/10000000000 : ℝ)|=(2070659029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377256103/10000000000 : ℝ)|^8267 ≤ (43835983787053/100000000000000 : ℝ)^6219
        have hw : |(5377256103/10000000000 : ℝ)|=(5377256103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377255523/10000000000 : ℝ)|^8267 ≤ (21917988750881/50000000000000 : ℝ)^6219
        have hw : |(5377255523/10000000000 : ℝ)|=(5377255523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295293423/10000000000 : ℝ)*x 0 + (-545408973/2500000000 : ℝ)*x 1 + (2688627953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295293423/10000000000 : ℝ)^8267 ≤ (4295001490463/10000000000000 : ℝ)^6219 := by
    have hnat : (5295293423 : ℕ)^8267*10000000000000^6219 ≤ 4295001490463^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295293423 10000000000 4295001490463 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545408973/2500000000 : ℝ)^8267 ≤ (528560136717/4000000000000 : ℝ)^6219 := by
    have hnat : (545408973 : ℕ)^8267*4000000000000^6219 ≤ 528560136717^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545408973 2500000000 528560136717 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688627953/5000000000 : ℝ)^8267 ≤ (43835981652221/100000000000000 : ℝ)^6219 := by
    have hnat : (2688627953 : ℕ)^8267*100000000000000^6219 ≤ 43835981652221^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688627953 5000000000 43835981652221 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295293423/10000000000 : ℝ), (-545408973/2500000000 : ℝ), (2688627953/5000000000 : ℝ)] ![(4295001490463/10000000000000 : ℝ), (528560136717/4000000000000 : ℝ), (43835981652221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295293423/10000000000 : ℝ)|^8267 ≤ (4295001490463/10000000000000 : ℝ)^6219
        have hw : |(5295293423/10000000000 : ℝ)|=(5295293423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545408973/2500000000 : ℝ)|^8267 ≤ (528560136717/4000000000000 : ℝ)^6219
        have hw : |(-545408973/2500000000 : ℝ)|=(545408973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688627953/5000000000 : ℝ)|^8267 ≤ (43835981652221/100000000000000 : ℝ)^6219
        have hw : |(2688627953/5000000000 : ℝ)|=(2688627953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323823379/2500000000 : ℝ)*x 0 + (215090237/400000000 : ℝ)*x 1 + (-68176117/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323823379/2500000000 : ℝ)^8267 ≤ (42950015907359/100000000000000 : ℝ)^6219 := by
    have hnat : (1323823379 : ℕ)^8267*100000000000000^6219 ≤ 42950015907359^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323823379 2500000000 42950015907359 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215090237/400000000 : ℝ)^8267 ≤ (43835981858119/100000000000000 : ℝ)^6219 := by
    have hnat : (215090237 : ℕ)^8267*100000000000000^6219 ≤ 43835981858119^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215090237 400000000 43835981858119 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68176117/312500000 : ℝ)^8267 ≤ (2642800445259/20000000000000 : ℝ)^6219 := by
    have hnat : (68176117 : ℕ)^8267*20000000000000^6219 ≤ 2642800445259^6219*312500000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68176117 312500000 2642800445259 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323823379/2500000000 : ℝ), (215090237/400000000 : ℝ), (-68176117/312500000 : ℝ)] ![(42950015907359/100000000000000 : ℝ), (43835981858119/100000000000000 : ℝ), (2642800445259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323823379/2500000000 : ℝ)|^8267 ≤ (42950015907359/100000000000000 : ℝ)^6219
        have hw : |(1323823379/2500000000 : ℝ)|=(1323823379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215090237/400000000 : ℝ)|^8267 ≤ (43835981858119/100000000000000 : ℝ)^6219
        have hw : |(215090237/400000000 : ℝ)|=(215090237/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68176117/312500000 : ℝ)|^8267 ≤ (2642800445259/20000000000000 : ℝ)^6219
        have hw : |(-68176117/312500000 : ℝ)|=(68176117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (70041159/156250000 : ℝ)*x 0 + (2161177897/5000000000 : ℝ)*x 1 + (864471101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70041159/156250000 : ℝ)^8267 ≤ (1376697541069/4000000000000 : ℝ)^6219 := by
    have hnat : (70041159 : ℕ)^8267*4000000000000^6219 ≤ 1376697541069^6219*156250000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70041159 156250000 1376697541069 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161177897/5000000000 : ℝ)^8267 ≤ (32791282181397/100000000000000 : ℝ)^6219 := by
    have hnat : (2161177897 : ℕ)^8267*100000000000000^6219 ≤ 32791282181397^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161177897 5000000000 32791282181397 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864471101/2000000000 : ℝ)^8267 ≤ (4098909908363/12500000000000 : ℝ)^6219 := by
    have hnat : (864471101 : ℕ)^8267*12500000000000^6219 ≤ 4098909908363^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864471101 2000000000 4098909908363 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70041159/156250000 : ℝ), (2161177897/5000000000 : ℝ), (864471101/2000000000 : ℝ)] ![(1376697541069/4000000000000 : ℝ), (32791282181397/100000000000000 : ℝ), (4098909908363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70041159/156250000 : ℝ)|^8267 ≤ (1376697541069/4000000000000 : ℝ)^6219
        have hw : |(70041159/156250000 : ℝ)|=(70041159/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161177897/5000000000 : ℝ)|^8267 ≤ (32791282181397/100000000000000 : ℝ)^6219
        have hw : |(2161177897/5000000000 : ℝ)|=(2161177897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864471101/2000000000 : ℝ)|^8267 ≤ (4098909908363/12500000000000 : ℝ)^6219
        have hw : |(864471101/2000000000 : ℝ)|=(864471101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-582601067/2500000000 : ℝ)*x 0 + (2640105293/5000000000 : ℝ)*x 1 + (1056042033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (582601067/2500000000 : ℝ)^8267 ≤ (7212534684643/50000000000000 : ℝ)^6219 := by
    have hnat : (582601067 : ℕ)^8267*50000000000000^6219 ≤ 7212534684643^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582601067 2500000000 7212534684643 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640105293/5000000000 : ℝ)^8267 ≤ (267421672329/625000000000 : ℝ)^6219 := by
    have hnat : (2640105293 : ℕ)^8267*625000000000^6219 ≤ 267421672329^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640105293 5000000000 267421672329 625000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056042033/2000000000 : ℝ)^8267 ≤ (21393731518833/50000000000000 : ℝ)^6219 := by
    have hnat : (1056042033 : ℕ)^8267*50000000000000^6219 ≤ 21393731518833^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056042033 2000000000 21393731518833 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-582601067/2500000000 : ℝ), (2640105293/5000000000 : ℝ), (1056042033/2000000000 : ℝ)] ![(7212534684643/50000000000000 : ℝ), (267421672329/625000000000 : ℝ), (21393731518833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-582601067/2500000000 : ℝ)|^8267 ≤ (7212534684643/50000000000000 : ℝ)^6219
        have hw : |(-582601067/2500000000 : ℝ)|=(582601067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640105293/5000000000 : ℝ)|^8267 ≤ (267421672329/625000000000 : ℝ)^6219
        have hw : |(2640105293/5000000000 : ℝ)|=(2640105293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056042033/2000000000 : ℝ)|^8267 ≤ (21393731518833/50000000000000 : ℝ)^6219
        have hw : |(1056042033/2000000000 : ℝ)|=(1056042033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363962343/10000000000 : ℝ)*x 0 + (-2219601343/10000000000 : ℝ)*x 1 + (5280210017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363962343/10000000000 : ℝ)^8267 ≤ (5461497731411/12500000000000 : ℝ)^6219 := by
    have hnat : (5363962343 : ℕ)^8267*12500000000000^6219 ≤ 5461497731411^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363962343 10000000000 5461497731411 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219601343/10000000000 : ℝ)^8267 ≤ (13520556682411/100000000000000 : ℝ)^6219 := by
    have hnat : (2219601343 : ℕ)^8267*100000000000000^6219 ≤ 13520556682411^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219601343 10000000000 13520556682411 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280210017/10000000000 : ℝ)^8267 ≤ (42787461443423/100000000000000 : ℝ)^6219 := by
    have hnat : (5280210017 : ℕ)^8267*100000000000000^6219 ≤ 42787461443423^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280210017 10000000000 42787461443423 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363962343/10000000000 : ℝ), (-2219601343/10000000000 : ℝ), (5280210017/10000000000 : ℝ)] ![(5461497731411/12500000000000 : ℝ), (13520556682411/100000000000000 : ℝ), (42787461443423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363962343/10000000000 : ℝ)|^8267 ≤ (5461497731411/12500000000000 : ℝ)^6219
        have hw : |(5363962343/10000000000 : ℝ)|=(5363962343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2219601343/10000000000 : ℝ)|^8267 ≤ (13520556682411/100000000000000 : ℝ)^6219
        have hw : |(-2219601343/10000000000 : ℝ)|=(2219601343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280210017/10000000000 : ℝ)|^8267 ≤ (42787461443423/100000000000000 : ℝ)^6219
        have hw : |(5280210017/10000000000 : ℝ)|=(5280210017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072792317/2000000000 : ℝ)*x 0 + (1320052703/2500000000 : ℝ)*x 1 + (-22196013/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072792317/2000000000 : ℝ)^8267 ≤ (10922993410939/25000000000000 : ℝ)^6219 := by
    have hnat : (1072792317 : ℕ)^8267*25000000000000^6219 ≤ 10922993410939^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072792317 2000000000 10922993410939 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320052703/2500000000 : ℝ)^8267 ≤ (10696867501773/25000000000000 : ℝ)^6219 := by
    have hnat : (1320052703 : ℕ)^8267*25000000000000^6219 ≤ 10696867501773^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320052703 2500000000 10696867501773 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22196013/100000000 : ℝ)^8267 ≤ (6760278167111/50000000000000 : ℝ)^6219 := by
    have hnat : (22196013 : ℕ)^8267*50000000000000^6219 ≤ 6760278167111^6219*100000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22196013 100000000 6760278167111 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072792317/2000000000 : ℝ), (1320052703/2500000000 : ℝ), (-22196013/100000000 : ℝ)] ![(10922993410939/25000000000000 : ℝ), (10696867501773/25000000000000 : ℝ), (6760278167111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072792317/2000000000 : ℝ)|^8267 ≤ (10922993410939/25000000000000 : ℝ)^6219
        have hw : |(1072792317/2000000000 : ℝ)|=(1072792317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320052703/2500000000 : ℝ)|^8267 ≤ (10696867501773/25000000000000 : ℝ)^6219
        have hw : |(1320052703/2500000000 : ℝ)|=(1320052703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22196013/100000000 : ℝ)|^8267 ≤ (6760278167111/50000000000000 : ℝ)^6219
        have hw : |(-22196013/100000000 : ℝ)|=(22196013/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1066430541/2500000000 : ℝ)*x 0 + (4430790417/10000000000 : ℝ)*x 1 + (2215395059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066430541/2500000000 : ℝ)^8267 ≤ (4027672727039/12500000000000 : ℝ)^6219 := by
    have hnat : (1066430541 : ℕ)^8267*12500000000000^6219 ≤ 4027672727039^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066430541 2500000000 4027672727039 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4430790417/10000000000 : ℝ)^8267 ≤ (132380119549/390625000000 : ℝ)^6219 := by
    have hnat : (4430790417 : ℕ)^8267*390625000000^6219 ≤ 132380119549^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430790417 10000000000 132380119549 390625000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215395059/5000000000 : ℝ)^8267 ≤ (33889307564499/100000000000000 : ℝ)^6219 := by
    have hnat : (2215395059 : ℕ)^8267*100000000000000^6219 ≤ 33889307564499^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215395059 5000000000 33889307564499 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066430541/2500000000 : ℝ), (4430790417/10000000000 : ℝ), (2215395059/5000000000 : ℝ)] ![(4027672727039/12500000000000 : ℝ), (132380119549/390625000000 : ℝ), (33889307564499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066430541/2500000000 : ℝ)|^8267 ≤ (4027672727039/12500000000000 : ℝ)^6219
        have hw : |(1066430541/2500000000 : ℝ)|=(1066430541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4430790417/10000000000 : ℝ)|^8267 ≤ (132380119549/390625000000 : ℝ)^6219
        have hw : |(4430790417/10000000000 : ℝ)|=(4430790417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215395059/5000000000 : ℝ)|^8267 ≤ (33889307564499/100000000000000 : ℝ)^6219
        have hw : |(2215395059/5000000000 : ℝ)|=(2215395059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_8 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2276169997/10000000000 : ℝ)*x 0 + (5214343731/10000000000 : ℝ)*x 1 + (2693428399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2276169997/10000000000 : ℝ)^8267 ≤ (13980528541457/100000000000000 : ℝ)^6219 := by
    have hnat : (2276169997 : ℕ)^8267*100000000000000^6219 ≤ 13980528541457^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276169997 10000000000 13980528541457 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214343731/10000000000 : ℝ)^8267 ≤ (1314981785519/3125000000000 : ℝ)^6219 := by
    have hnat : (5214343731 : ℕ)^8267*3125000000000^6219 ≤ 1314981785519^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214343731 10000000000 1314981785519 3125000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693428399/5000000000 : ℝ)^8267 ≤ (43940054300107/100000000000000 : ℝ)^6219 := by
    have hnat : (2693428399 : ℕ)^8267*100000000000000^6219 ≤ 43940054300107^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693428399 5000000000 43940054300107 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2276169997/10000000000 : ℝ), (5214343731/10000000000 : ℝ), (2693428399/5000000000 : ℝ)] ![(13980528541457/100000000000000 : ℝ), (1314981785519/3125000000000 : ℝ), (43940054300107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2276169997/10000000000 : ℝ)|^8267 ≤ (13980528541457/100000000000000 : ℝ)^6219
        have hw : |(-2276169997/10000000000 : ℝ)|=(2276169997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214343731/10000000000 : ℝ)|^8267 ≤ (1314981785519/3125000000000 : ℝ)^6219
        have hw : |(5214343731/10000000000 : ℝ)|=(5214343731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693428399/5000000000 : ℝ)|^8267 ≤ (43940054300107/100000000000000 : ℝ)^6219
        have hw : |(2693428399/5000000000 : ℝ)|=(2693428399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_9 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288496433/10000000000 : ℝ)*x 0 + (-2177808493/10000000000 : ℝ)*x 1 + (5386857243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288496433/10000000000 : ℝ)^8267 ≤ (42876745025447/100000000000000 : ℝ)^6219 := by
    have hnat : (5288496433 : ℕ)^8267*100000000000000^6219 ≤ 42876745025447^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288496433 10000000000 42876745025447 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177808493/10000000000 : ℝ)^8267 ≤ (13183195826699/100000000000000 : ℝ)^6219 := by
    have hnat : (2177808493 : ℕ)^8267*100000000000000^6219 ≤ 13183195826699^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177808493 10000000000 13183195826699 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386857243/10000000000 : ℝ)^8267 ≤ (10985014781319/25000000000000 : ℝ)^6219 := by
    have hnat : (5386857243 : ℕ)^8267*25000000000000^6219 ≤ 10985014781319^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386857243 10000000000 10985014781319 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288496433/10000000000 : ℝ), (-2177808493/10000000000 : ℝ), (5386857243/10000000000 : ℝ)] ![(42876745025447/100000000000000 : ℝ), (13183195826699/100000000000000 : ℝ), (10985014781319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288496433/10000000000 : ℝ)|^8267 ≤ (42876745025447/100000000000000 : ℝ)^6219
        have hw : |(5288496433/10000000000 : ℝ)|=(5288496433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177808493/10000000000 : ℝ)|^8267 ≤ (13183195826699/100000000000000 : ℝ)^6219
        have hw : |(-2177808493/10000000000 : ℝ)|=(2177808493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386857243/10000000000 : ℝ)|^8267 ≤ (10985014781319/25000000000000 : ℝ)^6219
        have hw : |(5386857243/10000000000 : ℝ)|=(5386857243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_10 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288496381/10000000000 : ℝ)*x 0 + (538685671/1000000000 : ℝ)*x 1 + (-1088904641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288496381/10000000000 : ℝ)^8267 ≤ (21438372232509/50000000000000 : ℝ)^6219 := by
    have hnat : (5288496381 : ℕ)^8267*50000000000000^6219 ≤ 21438372232509^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288496381 10000000000 21438372232509 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538685671/1000000000 : ℝ)^8267 ≤ (10985013336479/25000000000000 : ℝ)^6219 := by
    have hnat : (538685671 : ℕ)^8267*25000000000000^6219 ≤ 10985013336479^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538685671 1000000000 10985013336479 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088904641/5000000000 : ℝ)^8267 ≤ (13183202175701/100000000000000 : ℝ)^6219 := by
    have hnat : (1088904641 : ℕ)^8267*100000000000000^6219 ≤ 13183202175701^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088904641 5000000000 13183202175701 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288496381/10000000000 : ℝ), (538685671/1000000000 : ℝ), (-1088904641/5000000000 : ℝ)] ![(21438372232509/50000000000000 : ℝ), (10985013336479/25000000000000 : ℝ), (13183202175701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288496381/10000000000 : ℝ)|^8267 ≤ (21438372232509/50000000000000 : ℝ)^6219
        have hw : |(5288496381/10000000000 : ℝ)|=(5288496381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538685671/1000000000 : ℝ)|^8267 ≤ (10985013336479/25000000000000 : ℝ)^6219
        have hw : |(538685671/1000000000 : ℝ)|=(538685671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088904641/5000000000 : ℝ)|^8267 ≤ (13183202175701/100000000000000 : ℝ)^6219
        have hw : |(-1088904641/5000000000 : ℝ)|=(1088904641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_11 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4503821739/10000000000 : ℝ)*x 0 + (269476331/625000000 : ℝ)*x 1 + (4311621409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503821739/10000000000 : ℝ)^8267 ≤ (3463385541259/10000000000000 : ℝ)^6219 := by
    have hnat : (4503821739 : ℕ)^8267*10000000000000^6219 ≤ 3463385541259^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503821739 10000000000 3463385541259 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269476331/625000000 : ℝ)^8267 ≤ (16341535856351/50000000000000 : ℝ)^6219 := by
    have hnat : (269476331 : ℕ)^8267*50000000000000^6219 ≤ 16341535856351^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269476331 625000000 16341535856351 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311621409/10000000000 : ℝ)^8267 ≤ (16341536425673/50000000000000 : ℝ)^6219 := by
    have hnat : (4311621409 : ℕ)^8267*50000000000000^6219 ≤ 16341536425673^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311621409 10000000000 16341536425673 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503821739/10000000000 : ℝ), (269476331/625000000 : ℝ), (4311621409/10000000000 : ℝ)] ![(3463385541259/10000000000000 : ℝ), (16341535856351/50000000000000 : ℝ), (16341536425673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503821739/10000000000 : ℝ)|^8267 ≤ (3463385541259/10000000000000 : ℝ)^6219
        have hw : |(4503821739/10000000000 : ℝ)|=(4503821739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269476331/625000000 : ℝ)|^8267 ≤ (16341535856351/50000000000000 : ℝ)^6219
        have hw : |(269476331/625000000 : ℝ)|=(269476331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311621409/10000000000 : ℝ)|^8267 ≤ (16341536425673/50000000000000 : ℝ)^6219
        have hw : |(4311621409/10000000000 : ℝ)|=(4311621409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_12 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125256481/10000000000 : ℝ)*x 0 + (2720896873/5000000000 : ℝ)*x 1 + (1318051339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125256481/10000000000 : ℝ)^8267 ≤ (12762004622673/100000000000000 : ℝ)^6219 := by
    have hnat : (2125256481 : ℕ)^8267*100000000000000^6219 ≤ 12762004622673^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125256481 10000000000 12762004622673 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720896873/5000000000 : ℝ)^8267 ≤ (4453673787241/10000000000000 : ℝ)^6219 := by
    have hnat : (2720896873 : ℕ)^8267*10000000000000^6219 ≤ 4453673787241^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720896873 5000000000 4453673787241 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318051339/2500000000 : ℝ)^8267 ≤ (21350628744141/50000000000000 : ℝ)^6219 := by
    have hnat : (1318051339 : ℕ)^8267*50000000000000^6219 ≤ 21350628744141^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318051339 2500000000 21350628744141 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125256481/10000000000 : ℝ), (2720896873/5000000000 : ℝ), (1318051339/2500000000 : ℝ)] ![(12762004622673/100000000000000 : ℝ), (4453673787241/10000000000000 : ℝ), (21350628744141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125256481/10000000000 : ℝ)|^8267 ≤ (12762004622673/100000000000000 : ℝ)^6219
        have hw : |(-2125256481/10000000000 : ℝ)|=(2125256481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720896873/5000000000 : ℝ)|^8267 ≤ (4453673787241/10000000000000 : ℝ)^6219
        have hw : |(2720896873/5000000000 : ℝ)|=(2720896873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318051339/2500000000 : ℝ)|^8267 ≤ (21350628744141/50000000000000 : ℝ)^6219
        have hw : |(1318051339/2500000000 : ℝ)|=(1318051339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_13 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536962387/1000000000 : ℝ)*x 0 + (-138917147/625000000 : ℝ)*x 1 + (5272205527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536962387/1000000000 : ℝ)^8267 ≤ (43753294833457/100000000000000 : ℝ)^6219 := by
    have hnat : (536962387 : ℕ)^8267*100000000000000^6219 ≤ 43753294833457^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536962387 1000000000 43753294833457 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138917147/625000000 : ℝ)^8267 ≤ (6772722907731/50000000000000 : ℝ)^6219 := by
    have hnat : (138917147 : ℕ)^8267*50000000000000^6219 ≤ 6772722907731^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138917147 625000000 6772722907731 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272205527/10000000000 : ℝ)^8267 ≤ (21350629664679/50000000000000 : ℝ)^6219 := by
    have hnat : (5272205527 : ℕ)^8267*50000000000000^6219 ≤ 21350629664679^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272205527 10000000000 21350629664679 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536962387/1000000000 : ℝ), (-138917147/625000000 : ℝ), (5272205527/10000000000 : ℝ)] ![(43753294833457/100000000000000 : ℝ), (6772722907731/50000000000000 : ℝ), (21350629664679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536962387/1000000000 : ℝ)|^8267 ≤ (43753294833457/100000000000000 : ℝ)^6219
        have hw : |(536962387/1000000000 : ℝ)|=(536962387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138917147/625000000 : ℝ)|^8267 ≤ (6772722907731/50000000000000 : ℝ)^6219
        have hw : |(-138917147/625000000 : ℝ)|=(138917147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272205527/10000000000 : ℝ)|^8267 ≤ (21350629664679/50000000000000 : ℝ)^6219
        have hw : |(5272205527/10000000000 : ℝ)|=(5272205527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_14 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684811991/5000000000 : ℝ)*x 0 + (2636102629/5000000000 : ℝ)*x 1 + (-3472929/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684811991/5000000000 : ℝ)^8267 ≤ (218766480233/500000000000 : ℝ)^6219 := by
    have hnat : (2684811991 : ℕ)^8267*500000000000^6219 ≤ 218766480233^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684811991 5000000000 218766480233 500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636102629/5000000000 : ℝ)^8267 ≤ (21350628216581/50000000000000 : ℝ)^6219 := by
    have hnat : (2636102629 : ℕ)^8267*50000000000000^6219 ≤ 21350628216581^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636102629 5000000000 21350628216581 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3472929/15625000 : ℝ)^8267 ≤ (6772723750247/50000000000000 : ℝ)^6219 := by
    have hnat : (3472929 : ℕ)^8267*50000000000000^6219 ≤ 6772723750247^6219*15625000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472929 15625000 6772723750247 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684811991/5000000000 : ℝ), (2636102629/5000000000 : ℝ), (-3472929/15625000 : ℝ)] ![(218766480233/500000000000 : ℝ), (21350628216581/50000000000000 : ℝ), (6772723750247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684811991/5000000000 : ℝ)|^8267 ≤ (218766480233/500000000000 : ℝ)^6219
        have hw : |(2684811991/5000000000 : ℝ)|=(2684811991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636102629/5000000000 : ℝ)|^8267 ≤ (21350628216581/50000000000000 : ℝ)^6219
        have hw : |(2636102629/5000000000 : ℝ)|=(2636102629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3472929/15625000 : ℝ)|^8267 ≤ (6772723750247/50000000000000 : ℝ)^6219
        have hw : |(-3472929/15625000 : ℝ)|=(3472929/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_box_15 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (424759969/1000000000 : ℝ)*x 0 + (2219864733/5000000000 : ℝ)*x 1 + (2219864951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424759969/1000000000 : ℝ)^8267 ≤ (12515445557/39062500000 : ℝ)^6219 := by
    have hnat : (424759969 : ℕ)^8267*39062500000^6219 ≤ 12515445557^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424759969 1000000000 12515445557 39062500000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219864733/5000000000 : ℝ)^8267 ≤ (4247528432479/12500000000000 : ℝ)^6219 := by
    have hnat : (2219864733 : ℕ)^8267*12500000000000^6219 ≤ 4247528432479^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219864733 5000000000 4247528432479 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219864951/5000000000 : ℝ)^8267 ≤ (33980231895751/100000000000000 : ℝ)^6219 := by
    have hnat : (2219864951 : ℕ)^8267*100000000000000^6219 ≤ 33980231895751^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219864951 5000000000 33980231895751 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424759969/1000000000 : ℝ), (2219864733/5000000000 : ℝ), (2219864951/5000000000 : ℝ)] ![(12515445557/39062500000 : ℝ), (4247528432479/12500000000000 : ℝ), (33980231895751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424759969/1000000000 : ℝ)|^8267 ≤ (12515445557/39062500000 : ℝ)^6219
        have hw : |(424759969/1000000000 : ℝ)|=(424759969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219864733/5000000000 : ℝ)|^8267 ≤ (4247528432479/12500000000000 : ℝ)^6219
        have hw : |(2219864733/5000000000 : ℝ)|=(2219864733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219864951/5000000000 : ℝ)|^8267 ≤ (33980231895751/100000000000000 : ℝ)^6219
        have hw : |(2219864951/5000000000 : ℝ)|=(2219864951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59247/100000 : ℝ) ∧ (79597/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82971/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (1487133412319131/10000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^4133 ≤ (1487133412319131/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^4133*10000000000000000000^1024 ≤ 1487133412319131^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 1487133412319131 10000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (1487133412319131/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (35853830680273793/100000000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^4133 ≤ (35853830680273793/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14007 : ℕ)^4133*100000000000000000000^1024 ≤ 35853830680273793^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 35853830680273793 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (35853830680273793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001487133412319131/5000000000000000000 : ℝ) ≤ (2000147365525159/2000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (5001487133412319131/5000000000000000000 : ℝ)^1024 ≤ (2000147365525159/2000000000000000 : ℝ)^4133 := by
      have hnat : (5001487133412319131 : ℕ)^1024*2000000000000000^4133 ≤ 2000147365525159^4133*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001487133412319131 5000000000000000000 2000147365525159 2000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147365525159/2000000000000000 : ℝ)) (X := (5001487133412319131/5000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050725164803465103/100000000000000000000 : ℝ) ≤ (5000628268348981/5000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100050725164803465103/100000000000000000000 : ℝ)^1024 ≤ (5000628268348981/5000000000000000 : ℝ)^4133 := by
      have hnat : (100050725164803465103 : ℕ)^1024*5000000000000000^4133 ≤ 5000628268348981^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050725164803465103 100000000000000000000 5000628268348981 5000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000628268348981/5000000000000000 : ℝ)) (X := (100050725164803465103/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035853830680273793/50000000000000000000 : ℝ) ≤ (10001776245770129/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50035853830680273793/50000000000000000000 : ℝ)^1024 ≤ (10001776245770129/10000000000000000 : ℝ)^4133 := by
      have hnat : (50035853830680273793 : ℕ)^1024*10000000000000000^4133 ≤ 10001776245770129^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035853830680273793 50000000000000000000 10001776245770129 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001776245770129/10000000000000000 : ℝ)) (X := (50035853830680273793/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1487133412319131/10000000000000000000 : ℝ) ≤ ((1959308206317539117/1960000000000000000 : ℝ)+2*(519709072167/274400000000000 : ℝ)*(11263/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (1959308206317539117/1960000000000000000 : ℝ)+2*(519709072167/274400000000000 : ℝ)*(11263/100000 : ℝ)=(2000147365525159/2000000000000000 : ℝ) by norm_num, show 1+2*(1487133412319131/10000000000000000000 : ℝ)=(5001487133412319131/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35853830680273793/100000000000000000000 : ℝ)+(1487133412319131/10000000000000000000 : ℝ) ≤ ((1959308206317539117/1960000000000000000 : ℝ)+(519709072167/274400000000000 : ℝ)*((14007/100000 : ℝ)+(11263/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (1959308206317539117/1960000000000000000 : ℝ)+(519709072167/274400000000000 : ℝ)*((14007/100000 : ℝ)+(11263/100000 : ℝ))=(5000628268348981/5000000000000000 : ℝ) by norm_num, show 1+(35853830680273793/100000000000000000000 : ℝ)+(1487133412319131/10000000000000000000 : ℝ)=(100050725164803465103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35853830680273793/100000000000000000000 : ℝ) ≤ ((1959308206317539117/1960000000000000000 : ℝ)+2*(519709072167/274400000000000 : ℝ)*(14007/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (1959308206317539117/1960000000000000000 : ℝ)+2*(519709072167/274400000000000 : ℝ)*(14007/100000 : ℝ)=(10001776245770129/10000000000000000 : ℝ) by norm_num, show 1+2*(35853830680273793/100000000000000000000 : ℝ)=(50035853830680273793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1959308206317539117/1960000000000000000 : ℝ)*(X 1 0+X 2 0)+(519709072167/274400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1959308206317539117/1960000000000000000 : ℝ)) (alpha := (519709072167/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1959308206317539117/1960000000000000000 : ℝ)*(X 0 1+X 2 1)+(519709072167/274400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1959308206317539117/1960000000000000000 : ℝ)) (alpha := (519709072167/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1959308206317539117/1960000000000000000 : ℝ)*(X 0 2+X 1 2)+(519709072167/274400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (1959308206317539117/1960000000000000000 : ℝ)) (alpha := (519709072167/274400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2070659029/10000000000 : ℝ)*X 0 0+(5377256103/10000000000 : ℝ)*X 0 1+(5377255523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295293423/10000000000 : ℝ)*X 1 0+(-545408973/2500000000 : ℝ)*X 1 1+(2688627953/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323823379/2500000000 : ℝ)*X 2 0+(215090237/400000000 : ℝ)*X 2 1+(-68176117/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((70041159/156250000 : ℝ)*X 0 0+(2161177897/5000000000 : ℝ)*X 0 1+(864471101/2000000000 : ℝ)*X 0 2+(70041159/156250000 : ℝ)*X 1 0+(2161177897/5000000000 : ℝ)*X 1 1+(864471101/2000000000 : ℝ)*X 1 2+(70041159/156250000 : ℝ)*X 2 0+(2161177897/5000000000 : ℝ)*X 2 1+(864471101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-582601067/2500000000 : ℝ)*X 0 0+(2640105293/5000000000 : ℝ)*X 0 1+(1056042033/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363962343/10000000000 : ℝ)*X 1 0+(-2219601343/10000000000 : ℝ)*X 1 1+(5280210017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072792317/2000000000 : ℝ)*X 2 0+(1320052703/2500000000 : ℝ)*X 2 1+(-22196013/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066430541/2500000000 : ℝ)*X 0 0+(4430790417/10000000000 : ℝ)*X 0 1+(2215395059/5000000000 : ℝ)*X 0 2+(1066430541/2500000000 : ℝ)*X 1 0+(4430790417/10000000000 : ℝ)*X 1 1+(2215395059/5000000000 : ℝ)*X 1 2+(1066430541/2500000000 : ℝ)*X 2 0+(4430790417/10000000000 : ℝ)*X 2 1+(2215395059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2276169997/10000000000 : ℝ)*X 0 0+(5214343731/10000000000 : ℝ)*X 0 1+(2693428399/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288496433/10000000000 : ℝ)*X 1 0+(-2177808493/10000000000 : ℝ)*X 1 1+(5386857243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288496381/10000000000 : ℝ)*X 2 0+(538685671/1000000000 : ℝ)*X 2 1+(-1088904641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4503821739/10000000000 : ℝ)*X 0 0+(269476331/625000000 : ℝ)*X 0 1+(4311621409/10000000000 : ℝ)*X 0 2+(4503821739/10000000000 : ℝ)*X 1 0+(269476331/625000000 : ℝ)*X 1 1+(4311621409/10000000000 : ℝ)*X 1 2+(4503821739/10000000000 : ℝ)*X 2 0+(269476331/625000000 : ℝ)*X 2 1+(4311621409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2125256481/10000000000 : ℝ)*X 0 0+(2720896873/5000000000 : ℝ)*X 0 1+(1318051339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((536962387/1000000000 : ℝ)*X 1 0+(-138917147/625000000 : ℝ)*X 1 1+(5272205527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684811991/5000000000 : ℝ)*X 2 0+(2636102629/5000000000 : ℝ)*X 2 1+(-3472929/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((424759969/1000000000 : ℝ)*X 0 0+(2219864733/5000000000 : ℝ)*X 0 1+(2219864951/5000000000 : ℝ)*X 0 2+(424759969/1000000000 : ℝ)*X 1 0+(2219864733/5000000000 : ℝ)*X 1 1+(2219864951/5000000000 : ℝ)*X 1 2+(424759969/1000000000 : ℝ)*X 2 0+(2219864733/5000000000 : ℝ)*X 2 1+(2219864951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-7622249671036307361704503752771/12250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6156917/5000000000000 : ℝ)*(upper3) + (71794631/100000000000000 : ℝ)*(lower4) + (106776019/100000000000000 : ℝ)*(lower5) + (482942951332807/12500000000000 : ℝ)*(major0) + (482942951332807/12500000000000 : ℝ)*(major1) + (482942951332807/12500000000000 : ℝ)*(major2) + (5563296329/25000000000000 : ℝ)*(sp1) + (17734387/50000000000000 : ℝ)*(sp3) + (5139944085027329/100000000000000 : ℝ)*(sp4) + (1284980850576709/25000000000000 : ℝ)*(sp5) + (64245678176403/1250000000000 : ℝ)*(sp6) + (325985293224421/12500000000000 : ℝ)*(sp7) + (1570464823/100000000000000 : ℝ)*(sp8) + (36425172489/12500000000000 : ℝ)*(sp14) + (1303941190632071/50000000000000 : ℝ)*(f.failure) + (642493206936519/12500000000000 : ℝ)*(f.sum) + (185286227541/122500000000000000000000000 : ℝ)*base65 + (411850980690761419/24500000000000000000000000000000 : ℝ)*base67 + (467599605797761419/24500000000000000000000000000000 : ℝ)*base69 + (209621474152261419/24500000000000000000000000000000 : ℝ)*base71 + (311497682927/245000000000000000000000000 : ℝ)*base73 + (236264812307261419/24500000000000000000000000000000 : ℝ)*base75 + (93097108236261419/24500000000000000000000000000000 : ℝ)*base77 + (305022729850261419/24500000000000000000000000000000 : ℝ)*base79 + (310027393337/245000000000000000000000000 : ℝ)*base81 + (18730939/5000000000000000000000 : ℝ)*base90 + (18730939/5000000000000000000000 : ℝ)*base92 + (18730939/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59247/100000 : ℝ) ≤ (812900581299050020447281097983/1372000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8124593/20000000000000 : ℝ)*(upper0) + (23242471/25000000000000 : ℝ)*(upper3) + (4471269/3125000000000 : ℝ)*(upper4) + (15706405910919/400000000000 : ℝ)*(major0) + (15706405910919/400000000000 : ℝ)*(major1) + (15706405910919/400000000000 : ℝ)*(major2) + (2591495007668207/50000000000000 : ℝ)*(sp0) + (5182997693892419/100000000000000 : ℝ)*(sp1) + (5182983876782213/100000000000000 : ℝ)*(sp2) + (1325221616600867/50000000000000 : ℝ)*(sp3) + (9204828701/100000000000000 : ℝ)*(sp5) + (23021938907/100000000000000 : ℝ)*(sp6) + (1526184023/50000000000000 : ℝ)*(sp7) + (8441692353/50000000000000 : ℝ)*(sp8) + (132522314278489/5000000000000 : ℝ)*(f.failure) + (5183006898721121/100000000000000 : ℝ)*(f.sum) + (1160707217269/274400000000000000000000000 : ℝ)*base65 + (3089837413448339/5488000000000000000000000000000 : ℝ)*base68 + (57518099838824339/5488000000000000000000000000000 : ℝ)*base70 + (23581707021975661/5488000000000000000000000000000 : ℝ)*base71 + (50018930428939/1372000000000000000000000000 : ℝ)*base74 + (48385127310872339/5488000000000000000000000000000 : ℝ)*base76 + (5384241382648339/5488000000000000000000000000000 : ℝ)*base78 + (53369311667576339/5488000000000000000000000000000 : ℝ)*base80 + (3599095042847/1372000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4807899/500000000000000000000 : ℝ)*base89 + (4807899/500000000000000000000 : ℝ)*base91 + (4807899/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79597/100000 : ℝ) ≤ (68256965067408305353237429504227/85750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168761211/100000000000000 : ℝ)*(upper0) + (2125559/6250000000000 : ℝ)*(lower1) + (19070571/10000000000000 : ℝ)*(upper2) + (536194921/100000000000000 : ℝ)*(lower5) + (1098707492832389/25000000000000 : ℝ)*(major0) + (1098707492832389/25000000000000 : ℝ)*(major1) + (1098707492832389/25000000000000 : ℝ)*(major2) + (2987649953/100000000000000 : ℝ)*(sp0) + (23622698979/10000000000000 : ℝ)*(sp1) + (144575814003/100000000000000 : ℝ)*(sp3) + (5796624274602887/100000000000000 : ℝ)*(sp8) + (5796391035263049/100000000000000 : ℝ)*(sp9) + (5796627262252839/100000000000000 : ℝ)*(sp10) + (741588696209541/25000000000000 : ℝ)*(sp11) + (370812420081521/12500000000000 : ℝ)*(f.failure) + (5796627262252839/100000000000000 : ℝ)*(f.sum) + (18772902371323/3430000000000000000000000000 : ℝ)*base65 + (5493877053946573591/343000000000000000000000000000000 : ℝ)*base67 + (3023516501524573591/343000000000000000000000000000000 : ℝ)*base69 + (3743588998199573591/343000000000000000000000000000000 : ℝ)*base71 + (1907079868307/3430000000000000000000000000 : ℝ)*base74 + (3829978992638573591/343000000000000000000000000000000 : ℝ)*base75 + (5448257744903573591/343000000000000000000000000000000 : ℝ)*base77 + (3336258397015426409/343000000000000000000000000000000 : ℝ)*base80 + (11697095299027/3430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (560989/1250000000000000000000 : ℝ)*base90 + (560989/1250000000000000000000 : ℝ)*base92 + (560989/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-82971/100000 : ℝ) ≤ (-2903885824932828821367706838763/3500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6841903/20000000000000 : ℝ)*(lower0) + (3828589/3125000000000 : ℝ)*(lower1) + (82465697/100000000000000 : ℝ)*(lower4) + (1107355178517497/25000000000000 : ℝ)*(major0) + (1107355178517497/25000000000000 : ℝ)*(major1) + (1107355178517497/25000000000000 : ℝ)*(major2) + (89222747/800000000000 : ℝ)*(sp0) + (173456333047/100000000000000 : ℝ)*(sp5) + (27231283699/6250000000000 : ℝ)*(sp6) + (1493799061/20000000000000 : ℝ)*(sp7) + (1179327660865107/20000000000000 : ℝ)*(sp12) + (2948238000417931/50000000000000 : ℝ)*(sp13) + (2948106878314863/50000000000000 : ℝ)*(sp14) + (1494920278725653/50000000000000 : ℝ)*(sp15) + (2989848026446611/100000000000000 : ℝ)*(f.failure) + (589664945716891/10000000000000 : ℝ)*(f.sum) + (6971274643/490000000000000000000000000 : ℝ)*base66 + (20261406125280149/49000000000000000000000000000000 : ℝ)*base67 + (109217129646280149/49000000000000000000000000000000 : ℝ)*base69 + (156414584580280149/49000000000000000000000000000000 : ℝ)*base71 + (2098130204783/490000000000000000000000000 : ℝ)*base74 + (298040320734280149/49000000000000000000000000000000 : ℝ)*base75 + (84616819541280149/49000000000000000000000000000000 : ℝ)*base77 + (1381001942056280149/49000000000000000000000000000000 : ℝ)*base79 + (626933137723/490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1036201/10000000000000000000000 : ℝ)*base89 + (1036201/10000000000000000000000 : ℝ)*base91 + (1036201/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1074_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79597/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82971/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1074_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1074_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79597/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82971/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1074_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1074_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59247/100000 : ℝ) else (79597/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82971/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
