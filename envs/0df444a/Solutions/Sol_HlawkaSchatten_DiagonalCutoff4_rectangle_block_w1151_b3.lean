-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:07.937092+00:00
-- url     : https://prove2.me/submissions/ebca6b19-c9bd-4308-a363-c5a0d2da1525

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
theorem support_rectangle_w1151_s9_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081296947/5000000000 : ℝ)*x 0 + (2696410267/5000000000 : ℝ)*x 1 + (5265931481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081296947/5000000000 : ℝ)^1043 ≤ (13141704895089/100000000000000 : ℝ)^787 := by
    have hnat : (1081296947 : ℕ)^1043*100000000000000^787 ≤ 13141704895089^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081296947 5000000000 13141704895089 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696410267/5000000000 : ℝ)^1043 ≤ (44114309378193/100000000000000 : ℝ)^787 := by
    have hnat : (2696410267 : ℕ)^1043*100000000000000^787 ≤ 44114309378193^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696410267 5000000000 44114309378193 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265931481/10000000000 : ℝ)^1043 ≤ (21371992858879/50000000000000 : ℝ)^787 := by
    have hnat : (5265931481 : ℕ)^1043*50000000000000^787 ≤ 21371992858879^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265931481 10000000000 21371992858879 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081296947/5000000000 : ℝ), (2696410267/5000000000 : ℝ), (5265931481/10000000000 : ℝ)] ![(13141704895089/100000000000000 : ℝ), (44114309378193/100000000000000 : ℝ), (21371992858879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081296947/5000000000 : ℝ)|^1043 ≤ (13141704895089/100000000000000 : ℝ)^787
        have hw : |(-1081296947/5000000000 : ℝ)|=(1081296947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696410267/5000000000 : ℝ)|^1043 ≤ (44114309378193/100000000000000 : ℝ)^787
        have hw : |(2696410267/5000000000 : ℝ)|=(2696410267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265931481/10000000000 : ℝ)|^1043 ≤ (21371992858879/50000000000000 : ℝ)^787
        have hw : |(5265931481/10000000000 : ℝ)|=(5265931481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s9_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344711539/10000000000 : ℝ)*x 0 + (-2226951227/10000000000 : ℝ)*x 1 + (5265931483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344711539/10000000000 : ℝ)^1043 ≤ (43593513522697/100000000000000 : ℝ)^787 := by
    have hnat : (5344711539 : ℕ)^1043*100000000000000^787 ≤ 43593513522697^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344711539 10000000000 43593513522697 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226951227/10000000000 : ℝ)^1043 ≤ (13662500727359/100000000000000 : ℝ)^787 := by
    have hnat : (2226951227 : ℕ)^1043*100000000000000^787 ≤ 13662500727359^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226951227 10000000000 13662500727359 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265931483/10000000000 : ℝ)^1043 ≤ (42743985739273/100000000000000 : ℝ)^787 := by
    have hnat : (5265931483 : ℕ)^1043*100000000000000^787 ≤ 42743985739273^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265931483 10000000000 42743985739273 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344711539/10000000000 : ℝ), (-2226951227/10000000000 : ℝ), (5265931483/10000000000 : ℝ)] ![(43593513522697/100000000000000 : ℝ), (13662500727359/100000000000000 : ℝ), (42743985739273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344711539/10000000000 : ℝ)|^1043 ≤ (43593513522697/100000000000000 : ℝ)^787
        have hw : |(5344711539/10000000000 : ℝ)|=(5344711539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226951227/10000000000 : ℝ)|^1043 ≤ (13662500727359/100000000000000 : ℝ)^787
        have hw : |(-2226951227/10000000000 : ℝ)|=(2226951227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265931483/10000000000 : ℝ)|^1043 ≤ (42743985739273/100000000000000 : ℝ)^787
        have hw : |(5265931483/10000000000 : ℝ)|=(5265931483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s9_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344711519/10000000000 : ℝ)*x 0 + (5265931483/10000000000 : ℝ)*x 1 + (-1113475627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344711519/10000000000 : ℝ)^1043 ≤ (21796756653253/50000000000000 : ℝ)^787 := by
    have hnat : (5344711519 : ℕ)^1043*50000000000000^787 ≤ 21796756653253^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344711519 10000000000 21796756653253 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265931483/10000000000 : ℝ)^1043 ≤ (42743985739273/100000000000000 : ℝ)^787 := by
    have hnat : (5265931483 : ℕ)^1043*100000000000000^787 ≤ 42743985739273^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265931483 10000000000 42743985739273 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113475627/5000000000 : ℝ)^1043 ≤ (13662500946889/100000000000000 : ℝ)^787 := by
    have hnat : (1113475627 : ℕ)^1043*100000000000000^787 ≤ 13662500946889^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113475627 5000000000 13662500946889 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344711519/10000000000 : ℝ), (5265931483/10000000000 : ℝ), (-1113475627/5000000000 : ℝ)] ![(21796756653253/50000000000000 : ℝ), (42743985739273/100000000000000 : ℝ), (13662500946889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344711519/10000000000 : ℝ)|^1043 ≤ (21796756653253/50000000000000 : ℝ)^787
        have hw : |(5344711519/10000000000 : ℝ)|=(5344711519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265931483/10000000000 : ℝ)|^1043 ≤ (42743985739273/100000000000000 : ℝ)^787
        have hw : |(5265931483/10000000000 : ℝ)|=(5265931483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113475627/5000000000 : ℝ)|^1043 ≤ (13662500946889/100000000000000 : ℝ)^787
        have hw : |(-1113475627/5000000000 : ℝ)|=(1113475627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s9_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363409243/10000000000 : ℝ)*x 0 + (847756879/2000000000 : ℝ)*x 1 + (35933381/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363409243/10000000000 : ℝ)^1043 ≤ (16658519909161/50000000000000 : ℝ)^787 := by
    have hnat : (4363409243 : ℕ)^1043*50000000000000^787 ≤ 16658519909161^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363409243 10000000000 16658519909161 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847756879/2000000000 : ℝ)^1043 ≤ (200386382523/625000000000 : ℝ)^787 := by
    have hnat : (847756879 : ℕ)^1043*625000000000^787 ≤ 200386382523^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847756879 2000000000 200386382523 625000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35933381/80000000 : ℝ)^1043 ≤ (3462113896109/10000000000000 : ℝ)^787 := by
    have hnat : (35933381 : ℕ)^1043*10000000000000^787 ≤ 3462113896109^787*80000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35933381 80000000 3462113896109 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363409243/10000000000 : ℝ), (847756879/2000000000 : ℝ), (35933381/80000000 : ℝ)] ![(16658519909161/50000000000000 : ℝ), (200386382523/625000000000 : ℝ), (3462113896109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363409243/10000000000 : ℝ)|^1043 ≤ (16658519909161/50000000000000 : ℝ)^787
        have hw : |(4363409243/10000000000 : ℝ)|=(4363409243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847756879/2000000000 : ℝ)|^1043 ≤ (200386382523/625000000000 : ℝ)^787
        have hw : |(847756879/2000000000 : ℝ)|=(847756879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35933381/80000000 : ℝ)|^1043 ≤ (3462113896109/10000000000000 : ℝ)^787
        have hw : |(35933381/80000000 : ℝ)|=(35933381/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s9_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162598741/10000000000 : ℝ)*x 0 + (5266250137/10000000000 : ℝ)*x 1 + (5392500729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162598741/10000000000 : ℝ)^1043 ≤ (6570871965283/50000000000000 : ℝ)^787 := by
    have hnat : (2162598741 : ℕ)^1043*50000000000000^787 ≤ 6570871965283^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162598741 10000000000 6570871965283 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266250137/10000000000 : ℝ)^1043 ≤ (42747413677893/100000000000000 : ℝ)^787 := by
    have hnat : (5266250137 : ℕ)^1043*100000000000000^787 ≤ 42747413677893^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266250137 10000000000 42747413677893 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392500729/10000000000 : ℝ)^1043 ≤ (44110842375703/100000000000000 : ℝ)^787 := by
    have hnat : (5392500729 : ℕ)^1043*100000000000000^787 ≤ 44110842375703^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392500729 10000000000 44110842375703 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162598741/10000000000 : ℝ), (5266250137/10000000000 : ℝ), (5392500729/10000000000 : ℝ)] ![(6570871965283/50000000000000 : ℝ), (42747413677893/100000000000000 : ℝ), (44110842375703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162598741/10000000000 : ℝ)|^1043 ≤ (6570871965283/50000000000000 : ℝ)^787
        have hw : |(-2162598741/10000000000 : ℝ)|=(2162598741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266250137/10000000000 : ℝ)|^1043 ≤ (42747413677893/100000000000000 : ℝ)^787
        have hw : |(5266250137/10000000000 : ℝ)|=(5266250137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392500729/10000000000 : ℝ)|^1043 ≤ (44110842375703/100000000000000 : ℝ)^787
        have hw : |(5392500729/10000000000 : ℝ)|=(5392500729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s9_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363418931/10000000000 : ℝ)*x 0 + (2245518757/5000000000 : ℝ)*x 1 + (4239421781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363418931/10000000000 : ℝ)^1043 ≤ (33317137854037/100000000000000 : ℝ)^787 := by
    have hnat : (4363418931 : ℕ)^1043*100000000000000^787 ≤ 33317137854037^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363418931 10000000000 33317137854037 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245518757/5000000000 : ℝ)^1043 ≤ (34614651384789/100000000000000 : ℝ)^787 := by
    have hnat : (2245518757 : ℕ)^1043*100000000000000^787 ≤ 34614651384789^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245518757 5000000000 34614651384789 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239421781/10000000000 : ℝ)^1043 ≤ (32068210743457/100000000000000 : ℝ)^787 := by
    have hnat : (4239421781 : ℕ)^1043*100000000000000^787 ≤ 32068210743457^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239421781 10000000000 32068210743457 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363418931/10000000000 : ℝ), (2245518757/5000000000 : ℝ), (4239421781/10000000000 : ℝ)] ![(33317137854037/100000000000000 : ℝ), (34614651384789/100000000000000 : ℝ), (32068210743457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363418931/10000000000 : ℝ)|^1043 ≤ (33317137854037/100000000000000 : ℝ)^787
        have hw : |(4363418931/10000000000 : ℝ)|=(4363418931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245518757/5000000000 : ℝ)|^1043 ≤ (34614651384789/100000000000000 : ℝ)^787
        have hw : |(2245518757/5000000000 : ℝ)|=(2245518757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239421781/10000000000 : ℝ)|^1043 ≤ (32068210743457/100000000000000 : ℝ)^787
        have hw : |(4239421781/10000000000 : ℝ)|=(4239421781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5683/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (8343/2048 : ℝ) ≤ (14211648333564857/100000000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^8343 ≤ (14211648333564857/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2273 : ℕ)^8343*100000000000000000000^2048 ≤ 14211648333564857^2048*20000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 14211648333564857 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (14211648333564857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (33757221050163399/100000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^8343 ≤ (33757221050163399/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7027 : ℕ)^8343*100000000000000000000^2048 ≤ 33757221050163399^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 33757221050163399 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (33757221050163399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014211648333564857/50000000000000000000 : ℝ) ≤ (2500174411694331/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50014211648333564857/50000000000000000000 : ℝ)^2048 ≤ (2500174411694331/2500000000000000 : ℝ)^8343 := by
      have hnat : (50014211648333564857 : ℕ)^2048*2500000000000000^8343 ≤ 2500174411694331^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014211648333564857 50000000000000000000 2500174411694331 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174411694331/2500000000000000 : ℝ)) (X := (50014211648333564857/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (781624756792060377/781250000000000000 : ℝ) ≤ (10001177303980517/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (781624756792060377/781250000000000000 : ℝ)^2048 ≤ (10001177303980517/10000000000000000 : ℝ)^8343 := by
      have hnat : (781624756792060377 : ℕ)^2048*10000000000000000^8343 ≤ 10001177303980517^8343*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781624756792060377 781250000000000000 10001177303980517 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177303980517/10000000000000000 : ℝ)) (X := (781624756792060377/781250000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033757221050163399/50000000000000000000 : ℝ) ≤ (1000165696118371/1000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50033757221050163399/50000000000000000000 : ℝ)^2048 ≤ (1000165696118371/1000000000000000 : ℝ)^8343 := by
      have hnat : (50033757221050163399 : ℕ)^2048*1000000000000000^8343 ≤ 1000165696118371^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033757221050163399 50000000000000000000 1000165696118371 1000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000165696118371/1000000000000000 : ℝ)) (X := (50033757221050163399/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14211648333564857/100000000000000000000 : ℝ) ≤ ((13440486681977823673/13445000000000000000 : ℝ)+2*(479657203193/268900000000000 : ℝ)*(2273/20000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (13440486681977823673/13445000000000000000 : ℝ)+2*(479657203193/268900000000000 : ℝ)*(2273/20000 : ℝ)=(2500174411694331/2500000000000000 : ℝ) by norm_num, show 1+2*(14211648333564857/100000000000000000000 : ℝ)=(50014211648333564857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33757221050163399/100000000000000000000 : ℝ)+(14211648333564857/100000000000000000000 : ℝ) ≤ ((13440486681977823673/13445000000000000000 : ℝ)+(479657203193/268900000000000 : ℝ)*((7027/50000 : ℝ)+(2273/20000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (13440486681977823673/13445000000000000000 : ℝ)+(479657203193/268900000000000 : ℝ)*((7027/50000 : ℝ)+(2273/20000 : ℝ))=(10001177303980517/10000000000000000 : ℝ) by norm_num, show 1+(33757221050163399/100000000000000000000 : ℝ)+(14211648333564857/100000000000000000000 : ℝ)=(781624756792060377/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33757221050163399/100000000000000000000 : ℝ) ≤ ((13440486681977823673/13445000000000000000 : ℝ)+2*(479657203193/268900000000000 : ℝ)*(7027/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (13440486681977823673/13445000000000000000 : ℝ)+2*(479657203193/268900000000000 : ℝ)*(7027/50000 : ℝ)=(1000165696118371/1000000000000000 : ℝ) by norm_num, show 1+2*(33757221050163399/100000000000000000000 : ℝ)=(50033757221050163399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13440486681977823673/13445000000000000000 : ℝ)*(X 1 0+X 2 0)+(479657203193/268900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (13440486681977823673/13445000000000000000 : ℝ)) (alpha := (479657203193/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13440486681977823673/13445000000000000000 : ℝ)*(X 0 1+X 2 1)+(479657203193/268900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (13440486681977823673/13445000000000000000 : ℝ)) (alpha := (479657203193/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13440486681977823673/13445000000000000000 : ℝ)*(X 0 2+X 1 2)+(479657203193/268900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (13440486681977823673/13445000000000000000 : ℝ)) (alpha := (479657203193/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081296947/5000000000 : ℝ)*X 0 0+(2696410267/5000000000 : ℝ)*X 0 1+(5265931481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344711539/10000000000 : ℝ)*X 1 0+(-2226951227/10000000000 : ℝ)*X 1 1+(5265931483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344711519/10000000000 : ℝ)*X 2 0+(5265931483/10000000000 : ℝ)*X 2 1+(-1113475627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363409243/10000000000 : ℝ)*X 0 0+(847756879/2000000000 : ℝ)*X 0 1+(35933381/80000000 : ℝ)*X 0 2+(4363409243/10000000000 : ℝ)*X 1 0+(847756879/2000000000 : ℝ)*X 1 1+(35933381/80000000 : ℝ)*X 1 2+(4363409243/10000000000 : ℝ)*X 2 0+(847756879/2000000000 : ℝ)*X 2 1+(35933381/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162598741/10000000000 : ℝ)*X 0 0+(5266250137/10000000000 : ℝ)*X 0 1+(5392500729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4363418931/10000000000 : ℝ)*X 0 0+(2245518757/5000000000 : ℝ)*X 0 1+(4239421781/10000000000 : ℝ)*X 0 2+(4363418931/10000000000 : ℝ)*X 1 0+(2245518757/5000000000 : ℝ)*X 1 1+(4239421781/10000000000 : ℝ)*X 1 2+(4363418931/10000000000 : ℝ)*X 2 0+(2245518757/5000000000 : ℝ)*X 2 1+(4239421781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (468519662469026004399823257/134450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (714484797/100000000000000 : ℝ)*(base19) + (320311713/50000000000000 : ℝ)*(base23) + (23714893/100000000000000 : ℝ)*(lower2) + (54445893/50000000000000 : ℝ)*(upper3) + (3430897/12500000000000 : ℝ)*(upper5) + (2958819319564507/50000000000000 : ℝ)*(major0) + (2958819319564507/50000000000000 : ℝ)*(major1) + (1183527727825803/20000000000000 : ℝ)*(major2) + (3940461153222653/50000000000000 : ℝ)*(sp0) + (3940469918512157/50000000000000 : ℝ)*(sp1) + (1576187982177137/20000000000000 : ℝ)*(sp2) + (3954325464094997/100000000000000 : ℝ)*(sp3) + (3649012761/20000000000000 : ℝ)*(sp4) + (5573248407/50000000000000 : ℝ)*(sp5) + (395433661059181/10000000000000 : ℝ)*(f.failure) + (7880940551509111/100000000000000 : ℝ)*(f.sum) + (171228742961443/26890000000000000000000000000 : ℝ)*base66 + (190129533407450789/672250000000000000000000000000000 : ℝ)*base68 + (321152178510345581/268900000000000000000000000000000 : ℝ)*base70 + (762580962842200789/672250000000000000000000000000000 : ℝ)*base72 + (279463867421773/26890000000000000000000000000 : ℝ)*base74 + (37458814686245581/268900000000000000000000000000000 : ℝ)*base76 + (3492637827742724211/672250000000000000000000000000000 : ℝ)*base77 + (4062756618919224211/672250000000000000000000000000000 : ℝ)*base79 + (109534230977003/13445000000000000000000000000 : ℝ)*base82 + (120473/50000000000000000000 : ℝ)*base90 + (120473/50000000000000000000 : ℝ)*base92 + (620473/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1151_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_s10_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162591047/10000000000 : ℝ)*x 0 + (5392816807/10000000000 : ℝ)*x 1 + (658242171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162591047/10000000000 : ℝ)^1043 ≤ (3285420491673/25000000000000 : ℝ)^787 := by
    have hnat : (2162591047 : ℕ)^1043*25000000000000^787 ≤ 3285420491673^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162591047 10000000000 3285420491673 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392816807/10000000000 : ℝ)^1043 ≤ (44114268973441/100000000000000 : ℝ)^787 := by
    have hnat : (5392816807 : ℕ)^1043*100000000000000^787 ≤ 44114268973441^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392816807 10000000000 44114268973441 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658242171/1250000000 : ℝ)^1043 ≤ (8548809809377/20000000000000 : ℝ)^787 := by
    have hnat : (658242171 : ℕ)^1043*20000000000000^787 ≤ 8548809809377^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658242171 1250000000 8548809809377 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162591047/10000000000 : ℝ), (5392816807/10000000000 : ℝ), (658242171/1250000000 : ℝ)] ![(3285420491673/25000000000000 : ℝ), (44114268973441/100000000000000 : ℝ), (8548809809377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162591047/10000000000 : ℝ)|^1043 ≤ (3285420491673/25000000000000 : ℝ)^787
        have hw : |(-2162591047/10000000000 : ℝ)|=(2162591047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392816807/10000000000 : ℝ)|^1043 ≤ (44114268973441/100000000000000 : ℝ)^787
        have hw : |(5392816807/10000000000 : ℝ)|=(5392816807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658242171/1250000000 : ℝ)|^1043 ≤ (8548809809377/20000000000000 : ℝ)^787
        have hw : |(658242171/1250000000 : ℝ)|=(658242171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s10_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672355619/5000000000 : ℝ)*x 0 + (-556735981/2500000000 : ℝ)*x 1 + (1053187461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672355619/5000000000 : ℝ)^1043 ≤ (21796755134513/50000000000000 : ℝ)^787 := by
    have hnat : (2672355619 : ℕ)^1043*50000000000000^787 ≤ 21796755134513^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672355619 5000000000 21796755134513 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556735981/2500000000 : ℝ)^1043 ≤ (6831220674367/50000000000000 : ℝ)^787 := by
    have hnat : (556735981 : ℕ)^1043*50000000000000^787 ≤ 6831220674367^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556735981 2500000000 6831220674367 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053187461/2000000000 : ℝ)^1043 ≤ (21372024184583/50000000000000 : ℝ)^787 := by
    have hnat : (1053187461 : ℕ)^1043*50000000000000^787 ≤ 21372024184583^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053187461 2000000000 21372024184583 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672355619/5000000000 : ℝ), (-556735981/2500000000 : ℝ), (1053187461/2000000000 : ℝ)] ![(21796755134513/50000000000000 : ℝ), (6831220674367/50000000000000 : ℝ), (21372024184583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672355619/5000000000 : ℝ)|^1043 ≤ (21796755134513/50000000000000 : ℝ)^787
        have hw : |(2672355619/5000000000 : ℝ)|=(2672355619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556735981/2500000000 : ℝ)|^1043 ≤ (6831220674367/50000000000000 : ℝ)^787
        have hw : |(-556735981/2500000000 : ℝ)|=(556735981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053187461/2000000000 : ℝ)|^1043 ≤ (21372024184583/50000000000000 : ℝ)^787
        have hw : |(1053187461/2000000000 : ℝ)|=(1053187461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s10_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-540648947/2500000000 : ℝ)*x 0 + (1053251127/2000000000 : ℝ)*x 1 + (2696248733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540648947/2500000000 : ℝ)^1043 ≤ (6570860074239/50000000000000 : ℝ)^787 := by
    have hnat : (540648947 : ℕ)^1043*50000000000000^787 ≤ 6570860074239^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540648947 2500000000 6570860074239 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053251127/2000000000 : ℝ)^1043 ≤ (8549494564707/20000000000000 : ℝ)^787 := by
    have hnat : (1053251127 : ℕ)^1043*20000000000000^787 ≤ 8549494564707^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053251127 2000000000 8549494564707 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696248733/5000000000 : ℝ)^1043 ≤ (44110807001901/100000000000000 : ℝ)^787 := by
    have hnat : (2696248733 : ℕ)^1043*100000000000000^787 ≤ 44110807001901^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696248733 5000000000 44110807001901 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540648947/2500000000 : ℝ), (1053251127/2000000000 : ℝ), (2696248733/5000000000 : ℝ)] ![(6570860074239/50000000000000 : ℝ), (8549494564707/20000000000000 : ℝ), (44110807001901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540648947/2500000000 : ℝ)|^1043 ≤ (6570860074239/50000000000000 : ℝ)^787
        have hw : |(-540648947/2500000000 : ℝ)|=(540648947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053251127/2000000000 : ℝ)|^1043 ≤ (8549494564707/20000000000000 : ℝ)^787
        have hw : |(1053251127/2000000000 : ℝ)|=(1053251127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696248733/5000000000 : ℝ)|^1043 ≤ (44110807001901/100000000000000 : ℝ)^787
        have hw : |(2696248733/5000000000 : ℝ)|=(2696248733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s10_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062508893/2000000000 : ℝ)*x 0 + (-1050191757/5000000000 : ℝ)*x 1 + (674062169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062508893/2000000000 : ℝ)^1043 ≤ (5405767887627/12500000000000 : ℝ)^787 := by
    have hnat : (1062508893 : ℕ)^1043*12500000000000^787 ≤ 5405767887627^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062508893 2000000000 5405767887627 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050191757/5000000000 : ℝ)^1043 ≤ (12643051125183/100000000000000 : ℝ)^787 := by
    have hnat : (1050191757 : ℕ)^1043*100000000000000^787 ≤ 12643051125183^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050191757 5000000000 12643051125183 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674062169/1250000000 : ℝ)^1043 ≤ (1102770144151/2500000000000 : ℝ)^787 := by
    have hnat : (674062169 : ℕ)^1043*2500000000000^787 ≤ 1102770144151^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674062169 1250000000 1102770144151 2500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062508893/2000000000 : ℝ), (-1050191757/5000000000 : ℝ), (674062169/1250000000 : ℝ)] ![(5405767887627/12500000000000 : ℝ), (12643051125183/100000000000000 : ℝ), (1102770144151/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062508893/2000000000 : ℝ)|^1043 ≤ (5405767887627/12500000000000 : ℝ)^787
        have hw : |(1062508893/2000000000 : ℝ)|=(1062508893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050191757/5000000000 : ℝ)|^1043 ≤ (12643051125183/100000000000000 : ℝ)^787
        have hw : |(-1050191757/5000000000 : ℝ)|=(1050191757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674062169/1250000000 : ℝ)|^1043 ≤ (1102770144151/2500000000000 : ℝ)^787
        have hw : |(674062169/1250000000 : ℝ)|=(674062169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s10_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328136109/2500000000 : ℝ)*x 0 + (269624867/500000000 : ℝ)*x 1 + (-131273973/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328136109/2500000000 : ℝ)^1043 ≤ (21623071394077/50000000000000 : ℝ)^787 := by
    have hnat : (1328136109 : ℕ)^1043*50000000000000^787 ≤ 21623071394077^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328136109 2500000000 21623071394077 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269624867/500000000 : ℝ)^1043 ≤ (882216112719/2000000000000 : ℝ)^787 := by
    have hnat : (269624867 : ℕ)^1043*2000000000000^787 ≤ 882216112719^787*500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269624867 500000000 882216112719 2000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131273973/625000000 : ℝ)^1043 ≤ (3160762888991/25000000000000 : ℝ)^787 := by
    have hnat : (131273973 : ℕ)^1043*25000000000000^787 ≤ 3160762888991^787*625000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131273973 625000000 3160762888991 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328136109/2500000000 : ℝ), (269624867/500000000 : ℝ), (-131273973/625000000 : ℝ)] ![(21623071394077/50000000000000 : ℝ), (882216112719/2000000000000 : ℝ), (3160762888991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328136109/2500000000 : ℝ)|^1043 ≤ (21623071394077/50000000000000 : ℝ)^787
        have hw : |(1328136109/2500000000 : ℝ)|=(1328136109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269624867/500000000 : ℝ)|^1043 ≤ (882216112719/2000000000000 : ℝ)^787
        have hw : |(269624867/500000000 : ℝ)|=(269624867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131273973/625000000 : ℝ)|^1043 ≤ (3160762888991/25000000000000 : ℝ)^787
        have hw : |(-131273973/625000000 : ℝ)|=(131273973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s10_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2181709561/5000000000 : ℝ)*x 0 + (449102861/1000000000 : ℝ)*x 1 + (4239430661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181709561/5000000000 : ℝ)^1043 ≤ (33317139786823/100000000000000 : ℝ)^787 := by
    have hnat : (2181709561 : ℕ)^1043*100000000000000^787 ≤ 33317139786823^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181709561 5000000000 33317139786823 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449102861/1000000000 : ℝ)^1043 ≤ (8653640108427/25000000000000 : ℝ)^787 := by
    have hnat : (449102861 : ℕ)^1043*25000000000000^787 ≤ 8653640108427^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449102861 1000000000 8653640108427 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239430661/10000000000 : ℝ)^1043 ≤ (32068299764113/100000000000000 : ℝ)^787 := by
    have hnat : (4239430661 : ℕ)^1043*100000000000000^787 ≤ 32068299764113^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239430661 10000000000 32068299764113 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181709561/5000000000 : ℝ), (449102861/1000000000 : ℝ), (4239430661/10000000000 : ℝ)] ![(33317139786823/100000000000000 : ℝ), (8653640108427/25000000000000 : ℝ), (32068299764113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181709561/5000000000 : ℝ)|^1043 ≤ (33317139786823/100000000000000 : ℝ)^787
        have hw : |(2181709561/5000000000 : ℝ)|=(2181709561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449102861/1000000000 : ℝ)|^1043 ≤ (8653640108427/25000000000000 : ℝ)^787
        have hw : |(449102861/1000000000 : ℝ)|=(449102861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239430661/10000000000 : ℝ)|^1043 ≤ (32068299764113/100000000000000 : ℝ)^787
        have hw : |(4239430661/10000000000 : ℝ)|=(4239430661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5683/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5683/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (14216743120564069/100000000000000000000 : ℝ) := by
    have hpowers : (5683/50000 : ℝ)^8343 ≤ (14216743120564069/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5683 : ℕ)^8343*100000000000000000000^2048 ≤ 14216743120564069^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 50000 14216743120564069 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/50000 : ℝ)) (X := (14216743120564069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (33757221050163399/100000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^8343 ≤ (33757221050163399/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7027 : ℕ)^8343*100000000000000000000^2048 ≤ 33757221050163399^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 33757221050163399 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (33757221050163399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014216743120564069/50000000000000000000 : ℝ) ≤ (5000348948426253/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50014216743120564069/50000000000000000000 : ℝ)^2048 ≤ (5000348948426253/5000000000000000 : ℝ)^8343 := by
      have hnat : (50014216743120564069 : ℕ)^2048*5000000000000000^8343 ≤ 5000348948426253^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014216743120564069 50000000000000000000 5000348948426253 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348948426253/5000000000000000 : ℝ)) (X := (50014216743120564069/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011993491042681867/25000000000000000000 : ℝ) ≤ (10001177428999679/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (25011993491042681867/25000000000000000000 : ℝ)^2048 ≤ (10001177428999679/10000000000000000 : ℝ)^8343 := by
      have hnat : (25011993491042681867 : ℕ)^2048*10000000000000000^8343 ≤ 10001177428999679^8343*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011993491042681867 25000000000000000000 10001177428999679 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177428999679/10000000000000000 : ℝ)) (X := (25011993491042681867/25000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033757221050163399/50000000000000000000 : ℝ) ≤ (2500414240286713/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50033757221050163399/50000000000000000000 : ℝ)^2048 ≤ (2500414240286713/2500000000000000 : ℝ)^8343 := by
      have hnat : (50033757221050163399 : ℕ)^2048*2500000000000000^8343 ≤ 2500414240286713^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033757221050163399 50000000000000000000 2500414240286713 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414240286713/2500000000000000 : ℝ)) (X := (50033757221050163399/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14216743120564069/100000000000000000000 : ℝ) ≤ ((6717743805492499873/6720000000000000000 : ℝ)+2*(479532147173/268800000000000 : ℝ)*(5683/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (6717743805492499873/6720000000000000000 : ℝ)+2*(479532147173/268800000000000 : ℝ)*(5683/50000 : ℝ)=(5000348948426253/5000000000000000 : ℝ) by norm_num, show 1+2*(14216743120564069/100000000000000000000 : ℝ)=(50014216743120564069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33757221050163399/100000000000000000000 : ℝ)+(14216743120564069/100000000000000000000 : ℝ) ≤ ((6717743805492499873/6720000000000000000 : ℝ)+(479532147173/268800000000000 : ℝ)*((7027/50000 : ℝ)+(5683/50000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (6717743805492499873/6720000000000000000 : ℝ)+(479532147173/268800000000000 : ℝ)*((7027/50000 : ℝ)+(5683/50000 : ℝ))=(10001177428999679/10000000000000000 : ℝ) by norm_num, show 1+(33757221050163399/100000000000000000000 : ℝ)+(14216743120564069/100000000000000000000 : ℝ)=(25011993491042681867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33757221050163399/100000000000000000000 : ℝ) ≤ ((6717743805492499873/6720000000000000000 : ℝ)+2*(479532147173/268800000000000 : ℝ)*(7027/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (6717743805492499873/6720000000000000000 : ℝ)+2*(479532147173/268800000000000 : ℝ)*(7027/50000 : ℝ)=(2500414240286713/2500000000000000 : ℝ) by norm_num, show 1+2*(33757221050163399/100000000000000000000 : ℝ)=(50033757221050163399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6717743805492499873/6720000000000000000 : ℝ)*(X 1 0+X 2 0)+(479532147173/268800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6717743805492499873/6720000000000000000 : ℝ)) (alpha := (479532147173/268800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6717743805492499873/6720000000000000000 : ℝ)*(X 0 1+X 2 1)+(479532147173/268800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6717743805492499873/6720000000000000000 : ℝ)) (alpha := (479532147173/268800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6717743805492499873/6720000000000000000 : ℝ)*(X 0 2+X 1 2)+(479532147173/268800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (6717743805492499873/6720000000000000000 : ℝ)) (alpha := (479532147173/268800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2162591047/10000000000 : ℝ)*X 0 0+(5392816807/10000000000 : ℝ)*X 0 1+(658242171/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672355619/5000000000 : ℝ)*X 1 0+(-556735981/2500000000 : ℝ)*X 1 1+(1053187461/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-540648947/2500000000 : ℝ)*X 0 0+(1053251127/2000000000 : ℝ)*X 0 1+(2696248733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062508893/2000000000 : ℝ)*X 1 0+(-1050191757/5000000000 : ℝ)*X 1 1+(674062169/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1328136109/2500000000 : ℝ)*X 2 0+(269624867/500000000 : ℝ)*X 2 1+(-131273973/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2181709561/5000000000 : ℝ)*X 0 0+(449102861/1000000000 : ℝ)*X 0 1+(4239430661/10000000000 : ℝ)*X 0 2+(2181709561/5000000000 : ℝ)*X 1 0+(449102861/1000000000 : ℝ)*X 1 1+(4239430661/10000000000 : ℝ)*X 1 2+(2181709561/5000000000 : ℝ)*X 2 0+(449102861/1000000000 : ℝ)*X 2 1+(4239430661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s10_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86698083294274719749464807/28000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129570283/100000000000000 : ℝ)*(base19) + (49086683/20000000000000 : ℝ)*(base23) + (7979147/100000000000000 : ℝ)*(lower1) + (17467301/20000000000000 : ℝ)*(lower4) + (21897003/50000000000000 : ℝ)*(upper5) + (1486987990945159/25000000000000 : ℝ)*(major0) + (1486987990945159/25000000000000 : ℝ)*(major1) + (1486987990945159/25000000000000 : ℝ)*(major2) + (3922717939/100000000000000 : ℝ)*(sp0) + (1365879/156250000000 : ℝ)*(sp1) + (7921307054258499/100000000000000 : ℝ)*(sp2) + (1584261994648719/20000000000000 : ℝ)*(sp3) + (3960655365771511/50000000000000 : ℝ)*(sp4) + (1987296423686411/50000000000000 : ℝ)*(sp5) + (1987296423686411/50000000000000 : ℝ)*(f.failure) + (7921310976976437/100000000000000 : ℝ)*(f.sum) + (17963877210467/3360000000000000000000000000 : ℝ)*base65 + (74089747216286731/56000000000000000000000000000000 : ℝ)*base68 + (147033855936286731/56000000000000000000000000000000 : ℝ)*base70 + (158899754647713269/56000000000000000000000000000000 : ℝ)*base71 + (16201721141507/3360000000000000000000000000 : ℝ)*base73 + (861384032560286731/56000000000000000000000000000000 : ℝ)*base76 + (78312025024286731/56000000000000000000000000000000 : ℝ)*base78 + (566238397631713269/56000000000000000000000000000000 : ℝ)*base79 + (184910477053/3360000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1344063/250000000000000000000 : ℝ)*base90 + (1344063/250000000000000000000 : ℝ)*base92 + (1344063/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1151_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_box_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036006487/10000000000 : ℝ)*x 0 + (5376176801/10000000000 : ℝ)*x 1 + (1075235479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036006487/10000000000 : ℝ)^1043 ≤ (12132066059719/100000000000000 : ℝ)^787 := by
    have hnat : (2036006487 : ℕ)^1043*100000000000000^787 ≤ 12132066059719^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036006487 10000000000 12132066059719 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376176801/10000000000 : ℝ)^1043 ≤ (43933963746289/100000000000000 : ℝ)^787 := by
    have hnat : (5376176801 : ℕ)^1043*100000000000000^787 ≤ 43933963746289^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376176801 10000000000 43933963746289 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075235479/2000000000 : ℝ)^1043 ≤ (43933970179427/100000000000000 : ℝ)^787 := by
    have hnat : (1075235479 : ℕ)^1043*100000000000000^787 ≤ 43933970179427^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075235479 2000000000 43933970179427 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036006487/10000000000 : ℝ), (5376176801/10000000000 : ℝ), (1075235479/2000000000 : ℝ)] ![(12132066059719/100000000000000 : ℝ), (43933963746289/100000000000000 : ℝ), (43933970179427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036006487/10000000000 : ℝ)|^1043 ≤ (12132066059719/100000000000000 : ℝ)^787
        have hw : |(-2036006487/10000000000 : ℝ)|=(2036006487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376176801/10000000000 : ℝ)|^1043 ≤ (43933963746289/100000000000000 : ℝ)^787
        have hw : |(5376176801/10000000000 : ℝ)|=(5376176801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075235479/2000000000 : ℝ)|^1043 ≤ (43933970179427/100000000000000 : ℝ)^787
        have hw : |(1075235479/2000000000 : ℝ)|=(1075235479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1059213883/2000000000 : ℝ)*x 0 + (-2144668069/10000000000 : ℝ)*x 1 + (1075235509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059213883/2000000000 : ℝ)^1043 ≤ (43068494471333/100000000000000 : ℝ)^787 := by
    have hnat : (1059213883 : ℕ)^1043*100000000000000^787 ≤ 43068494471333^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059213883 2000000000 43068494471333 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144668069/10000000000 : ℝ)^1043 ≤ (12997533706463/100000000000000 : ℝ)^787 := by
    have hnat : (2144668069 : ℕ)^1043*100000000000000^787 ≤ 12997533706463^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144668069 10000000000 12997533706463 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075235509/2000000000 : ℝ)^1043 ≤ (43933971803957/100000000000000 : ℝ)^787 := by
    have hnat : (1075235509 : ℕ)^1043*100000000000000^787 ≤ 43933971803957^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075235509 2000000000 43933971803957 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059213883/2000000000 : ℝ), (-2144668069/10000000000 : ℝ), (1075235509/2000000000 : ℝ)] ![(43068494471333/100000000000000 : ℝ), (12997533706463/100000000000000 : ℝ), (43933971803957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059213883/2000000000 : ℝ)|^1043 ≤ (43068494471333/100000000000000 : ℝ)^787
        have hw : |(1059213883/2000000000 : ℝ)|=(1059213883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144668069/10000000000 : ℝ)|^1043 ≤ (12997533706463/100000000000000 : ℝ)^787
        have hw : |(-2144668069/10000000000 : ℝ)|=(2144668069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075235509/2000000000 : ℝ)|^1043 ≤ (43933971803957/100000000000000 : ℝ)^787
        have hw : |(1075235509/2000000000 : ℝ)|=(1075235509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (105921401/200000000 : ℝ)*x 0 + (1344044287/2500000000 : ℝ)*x 1 + (-268083469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105921401/200000000 : ℝ)^1043 ≤ (672945333047/1562500000000 : ℝ)^787 := by
    have hnat : (105921401 : ℕ)^1043*1562500000000^787 ≤ 672945333047^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105921401 200000000 672945333047 1562500000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344044287/2500000000 : ℝ)^1043 ≤ (2745872969023/6250000000000 : ℝ)^787 := by
    have hnat : (1344044287 : ℕ)^1043*6250000000000^787 ≤ 2745872969023^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344044287 2500000000 2745872969023 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268083469/1250000000 : ℝ)^1043 ≤ (12997531160397/100000000000000 : ℝ)^787 := by
    have hnat : (268083469 : ℕ)^1043*100000000000000^787 ≤ 12997531160397^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268083469 1250000000 12997531160397 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105921401/200000000 : ℝ), (1344044287/2500000000 : ℝ), (-268083469/1250000000 : ℝ)] ![(672945333047/1562500000000 : ℝ), (2745872969023/6250000000000 : ℝ), (12997531160397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105921401/200000000 : ℝ)|^1043 ≤ (672945333047/1562500000000 : ℝ)^787
        have hw : |(105921401/200000000 : ℝ)|=(105921401/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344044287/2500000000 : ℝ)|^1043 ≤ (2745872969023/6250000000000 : ℝ)^787
        have hw : |(1344044287/2500000000 : ℝ)|=(1344044287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268083469/1250000000 : ℝ)|^1043 ≤ (12997531160397/100000000000000 : ℝ)^787
        have hw : |(-268083469/1250000000 : ℝ)|=(268083469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4470849897/10000000000 : ℝ)*x 0 + (67371731/156250000 : ℝ)*x 1 + (4311790397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470849897/10000000000 : ℝ)^1043 ≤ (8602148288851/25000000000000 : ℝ)^787 := by
    have hnat : (4470849897 : ℕ)^1043*25000000000000^787 ≤ 8602148288851^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470849897 10000000000 8602148288851 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67371731/156250000 : ℝ)^1043 ≤ (16397852681949/50000000000000 : ℝ)^787 := by
    have hnat : (67371731 : ℕ)^1043*50000000000000^787 ≤ 16397852681949^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67371731 156250000 16397852681949 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311790397/10000000000 : ℝ)^1043 ≤ (32795701462863/100000000000000 : ℝ)^787 := by
    have hnat : (4311790397 : ℕ)^1043*100000000000000^787 ≤ 32795701462863^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311790397 10000000000 32795701462863 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470849897/10000000000 : ℝ), (67371731/156250000 : ℝ), (4311790397/10000000000 : ℝ)] ![(8602148288851/25000000000000 : ℝ), (16397852681949/50000000000000 : ℝ), (32795701462863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470849897/10000000000 : ℝ)|^1043 ≤ (8602148288851/25000000000000 : ℝ)^787
        have hw : |(4470849897/10000000000 : ℝ)|=(4470849897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67371731/156250000 : ℝ)|^1043 ≤ (16397852681949/50000000000000 : ℝ)^787
        have hw : |(67371731/156250000 : ℝ)|=(67371731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311790397/10000000000 : ℝ)|^1043 ≤ (32795701462863/100000000000000 : ℝ)^787
        have hw : |(4311790397/10000000000 : ℝ)|=(4311790397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1145282769/5000000000 : ℝ)*x 0 + (5281257869/10000000000 : ℝ)*x 1 + (2640629309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1145282769/5000000000 : ℝ)^1043 ≤ (14182118749187/100000000000000 : ℝ)^787 := by
    have hnat : (1145282769 : ℕ)^1043*100000000000000^787 ≤ 14182118749187^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145282769 5000000000 14182118749187 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281257869/10000000000 : ℝ)^1043 ≤ (8581787316961/20000000000000 : ℝ)^787 := by
    have hnat : (5281257869 : ℕ)^1043*20000000000000^787 ≤ 8581787316961^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281257869 10000000000 8581787316961 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640629309/5000000000 : ℝ)^1043 ≤ (42908944649757/100000000000000 : ℝ)^787 := by
    have hnat : (2640629309 : ℕ)^1043*100000000000000^787 ≤ 42908944649757^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640629309 5000000000 42908944649757 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1145282769/5000000000 : ℝ), (5281257869/10000000000 : ℝ), (2640629309/5000000000 : ℝ)] ![(14182118749187/100000000000000 : ℝ), (8581787316961/20000000000000 : ℝ), (42908944649757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1145282769/5000000000 : ℝ)|^1043 ≤ (14182118749187/100000000000000 : ℝ)^787
        have hw : |(-1145282769/5000000000 : ℝ)|=(1145282769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281257869/10000000000 : ℝ)|^1043 ≤ (8581787316961/20000000000000 : ℝ)^787
        have hw : |(5281257869/10000000000 : ℝ)|=(5281257869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640629309/5000000000 : ℝ)|^1043 ≤ (42908944649757/100000000000000 : ℝ)^787
        have hw : |(2640629309/5000000000 : ℝ)|=(2640629309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (670389537/1250000000 : ℝ)*x 0 + (-2182033249/10000000000 : ℝ)*x 1 + (5281258133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670389537/1250000000 : ℝ)^1043 ≤ (8758514360347/20000000000000 : ℝ)^787 := by
    have hnat : (670389537 : ℕ)^1043*20000000000000^787 ≤ 8758514360347^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670389537 1250000000 8758514360347 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182033249/10000000000 : ℝ)^1043 ≤ (6649244378059/50000000000000 : ℝ)^787 := by
    have hnat : (2182033249 : ℕ)^1043*50000000000000^787 ≤ 6649244378059^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182033249 10000000000 6649244378059 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281258133/10000000000 : ℝ)^1043 ≤ (21454469713729/50000000000000 : ℝ)^787 := by
    have hnat : (5281258133 : ℕ)^1043*50000000000000^787 ≤ 21454469713729^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281258133 10000000000 21454469713729 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670389537/1250000000 : ℝ), (-2182033249/10000000000 : ℝ), (5281258133/10000000000 : ℝ)] ![(8758514360347/20000000000000 : ℝ), (6649244378059/50000000000000 : ℝ), (21454469713729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670389537/1250000000 : ℝ)|^1043 ≤ (8758514360347/20000000000000 : ℝ)^787
        have hw : |(670389537/1250000000 : ℝ)|=(670389537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182033249/10000000000 : ℝ)|^1043 ≤ (6649244378059/50000000000000 : ℝ)^787
        have hw : |(-2182033249/10000000000 : ℝ)|=(2182033249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281258133/10000000000 : ℝ)|^1043 ≤ (21454469713729/50000000000000 : ℝ)^787
        have hw : |(5281258133/10000000000 : ℝ)|=(5281258133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2681558583/5000000000 : ℝ)*x 0 + (1320314519/2500000000 : ℝ)*x 1 + (-2182032159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681558583/5000000000 : ℝ)^1043 ≤ (10948145304139/25000000000000 : ℝ)^787 := by
    have hnat : (2681558583 : ℕ)^1043*25000000000000^787 ≤ 10948145304139^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681558583 5000000000 10948145304139 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320314519/2500000000 : ℝ)^1043 ≤ (42908938813703/100000000000000 : ℝ)^787 := by
    have hnat : (1320314519 : ℕ)^1043*100000000000000^787 ≤ 42908938813703^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320314519 2500000000 42908938813703 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182032159/10000000000 : ℝ)^1043 ≤ (664923997609/5000000000000 : ℝ)^787 := by
    have hnat : (2182032159 : ℕ)^1043*5000000000000^787 ≤ 664923997609^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182032159 10000000000 664923997609 5000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681558583/5000000000 : ℝ), (1320314519/2500000000 : ℝ), (-2182032159/10000000000 : ℝ)] ![(10948145304139/25000000000000 : ℝ), (42908938813703/100000000000000 : ℝ), (664923997609/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681558583/5000000000 : ℝ)|^1043 ≤ (10948145304139/25000000000000 : ℝ)^787
        have hw : |(2681558583/5000000000 : ℝ)|=(2681558583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320314519/2500000000 : ℝ)|^1043 ≤ (42908938813703/100000000000000 : ℝ)^787
        have hw : |(1320314519/2500000000 : ℝ)|=(1320314519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182032159/10000000000 : ℝ)|^1043 ≤ (664923997609/5000000000000 : ℝ)^787
        have hw : |(-2182032159/10000000000 : ℝ)|=(2182032159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2127801907/5000000000 : ℝ)*x 0 + (883878617/2000000000 : ℝ)*x 1 + (88387853/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127801907/5000000000 : ℝ)^1043 ≤ (6446106748827/20000000000000 : ℝ)^787 := by
    have hnat : (2127801907 : ℕ)^1043*20000000000000^787 ≤ 6446106748827^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127801907 5000000000 6446106748827 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883878617/2000000000 : ℝ)^1043 ≤ (271077882669/800000000000 : ℝ)^787 := by
    have hnat : (883878617 : ℕ)^1043*800000000000^787 ≤ 271077882669^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883878617 2000000000 271077882669 800000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88387853/200000000 : ℝ)^1043 ≤ (16942365456721/50000000000000 : ℝ)^787 := by
    have hnat : (88387853 : ℕ)^1043*50000000000000^787 ≤ 16942365456721^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88387853 200000000 16942365456721 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127801907/5000000000 : ℝ), (883878617/2000000000 : ℝ), (88387853/200000000 : ℝ)] ![(6446106748827/20000000000000 : ℝ), (271077882669/800000000000 : ℝ), (16942365456721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127801907/5000000000 : ℝ)|^1043 ≤ (6446106748827/20000000000000 : ℝ)^787
        have hw : |(2127801907/5000000000 : ℝ)|=(2127801907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883878617/2000000000 : ℝ)|^1043 ≤ (271077882669/800000000000 : ℝ)^787
        have hw : |(883878617/2000000000 : ℝ)|=(883878617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88387853/200000000 : ℝ)|^1043 ≤ (16942365456721/50000000000000 : ℝ)^787
        have hw : |(88387853/200000000 : ℝ)|=(88387853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_8 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-44746457/200000000 : ℝ)*x 0 + (5216687123/10000000000 : ℝ)*x 1 + (5385785427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44746457/200000000 : ℝ)^1043 ≤ (859180832049/6250000000000 : ℝ)^787 := by
    have hnat : (44746457 : ℕ)^1043*6250000000000^787 ≤ 859180832049^787*200000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44746457 200000000 859180832049 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216687123/10000000000 : ℝ)^1043 ≤ (21107524676627/50000000000000 : ℝ)^787 := by
    have hnat : (5216687123 : ℕ)^1043*50000000000000^787 ≤ 21107524676627^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216687123 10000000000 21107524676627 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385785427/10000000000 : ℝ)^1043 ≤ (44038057311731/100000000000000 : ℝ)^787 := by
    have hnat : (5385785427 : ℕ)^1043*100000000000000^787 ≤ 44038057311731^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385785427 10000000000 44038057311731 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44746457/200000000 : ℝ), (5216687123/10000000000 : ℝ), (5385785427/10000000000 : ℝ)] ![(859180832049/6250000000000 : ℝ), (21107524676627/50000000000000 : ℝ), (44038057311731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44746457/200000000 : ℝ)|^1043 ≤ (859180832049/6250000000000 : ℝ)^787
        have hw : |(-44746457/200000000 : ℝ)|=(44746457/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216687123/10000000000 : ℝ)|^1043 ≤ (21107524676627/50000000000000 : ℝ)^787
        have hw : |(5216687123/10000000000 : ℝ)|=(5216687123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385785427/10000000000 : ℝ)|^1043 ≤ (44038057311731/100000000000000 : ℝ)^787
        have hw : |(5385785427/10000000000 : ℝ)|=(5385785427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_9 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289279501/10000000000 : ℝ)*x 0 + (-1070408277/5000000000 : ℝ)*x 1 + (2692892829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289279501/10000000000 : ℝ)^1043 ≤ (42995331846649/100000000000000 : ℝ)^787 := by
    have hnat : (5289279501 : ℕ)^1043*100000000000000^787 ≤ 42995331846649^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289279501 10000000000 42995331846649 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070408277/5000000000 : ℝ)^1043 ≤ (12966608321377/100000000000000 : ℝ)^787 := by
    have hnat : (1070408277 : ℕ)^1043*100000000000000^787 ≤ 12966608321377^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070408277 5000000000 12966608321377 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692892829/5000000000 : ℝ)^1043 ≤ (550475747687/1250000000000 : ℝ)^787 := by
    have hnat : (2692892829 : ℕ)^1043*1250000000000^787 ≤ 550475747687^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692892829 5000000000 550475747687 1250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289279501/10000000000 : ℝ), (-1070408277/5000000000 : ℝ), (2692892829/5000000000 : ℝ)] ![(42995331846649/100000000000000 : ℝ), (12966608321377/100000000000000 : ℝ), (550475747687/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289279501/10000000000 : ℝ)|^1043 ≤ (42995331846649/100000000000000 : ℝ)^787
        have hw : |(5289279501/10000000000 : ℝ)|=(5289279501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070408277/5000000000 : ℝ)|^1043 ≤ (12966608321377/100000000000000 : ℝ)^787
        have hw : |(-1070408277/5000000000 : ℝ)|=(1070408277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692892829/5000000000 : ℝ)|^1043 ≤ (550475747687/1250000000000 : ℝ)^787
        have hw : |(2692892829/5000000000 : ℝ)|=(2692892829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_10 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057855733/2000000000 : ℝ)*x 0 + (2692893179/5000000000 : ℝ)*x 1 + (-214081673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057855733/2000000000 : ℝ)^1043 ≤ (42995322840469/100000000000000 : ℝ)^787 := by
    have hnat : (1057855733 : ℕ)^1043*100000000000000^787 ≤ 42995322840469^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057855733 2000000000 42995322840469 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692893179/5000000000 : ℝ)^1043 ≤ (5504758425063/12500000000000 : ℝ)^787 := by
    have hnat : (2692893179 : ℕ)^1043*12500000000000^787 ≤ 5504758425063^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692893179 5000000000 5504758425063 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214081673/1000000000 : ℝ)^1043 ≤ (12966609734139/100000000000000 : ℝ)^787 := by
    have hnat : (214081673 : ℕ)^1043*100000000000000^787 ≤ 12966609734139^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214081673 1000000000 12966609734139 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057855733/2000000000 : ℝ), (2692893179/5000000000 : ℝ), (-214081673/1000000000 : ℝ)] ![(42995322840469/100000000000000 : ℝ), (5504758425063/12500000000000 : ℝ), (12966609734139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057855733/2000000000 : ℝ)|^1043 ≤ (42995322840469/100000000000000 : ℝ)^787
        have hw : |(1057855733/2000000000 : ℝ)|=(1057855733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692893179/5000000000 : ℝ)|^1043 ≤ (5504758425063/12500000000000 : ℝ)^787
        have hw : |(2692893179/5000000000 : ℝ)|=(2692893179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214081673/1000000000 : ℝ)|^1043 ≤ (12966609734139/100000000000000 : ℝ)^787
        have hw : |(-214081673/1000000000 : ℝ)|=(214081673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_11 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4492366121/10000000000 : ℝ)*x 0 + (4300891681/10000000000 : ℝ)*x 1 + (17203569/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492366121/10000000000 : ℝ)^1043 ≤ (34628223273383/100000000000000 : ℝ)^787 := by
    have hnat : (4492366121 : ℕ)^1043*100000000000000^787 ≤ 34628223273383^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492366121 10000000000 34628223273383 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300891681/10000000000 : ℝ)^1043 ≤ (6537177097851/20000000000000 : ℝ)^787 := by
    have hnat : (4300891681 : ℕ)^1043*20000000000000^787 ≤ 6537177097851^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300891681 10000000000 6537177097851 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17203569/40000000 : ℝ)^1043 ≤ (16342945610083/50000000000000 : ℝ)^787 := by
    have hnat : (17203569 : ℕ)^1043*50000000000000^787 ≤ 16342945610083^787*40000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17203569 40000000 16342945610083 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492366121/10000000000 : ℝ), (4300891681/10000000000 : ℝ), (17203569/40000000 : ℝ)] ![(34628223273383/100000000000000 : ℝ), (6537177097851/20000000000000 : ℝ), (16342945610083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492366121/10000000000 : ℝ)|^1043 ≤ (34628223273383/100000000000000 : ℝ)^787
        have hw : |(4492366121/10000000000 : ℝ)|=(4492366121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4300891681/10000000000 : ℝ)|^1043 ≤ (6537177097851/20000000000000 : ℝ)^787
        have hw : |(4300891681/10000000000 : ℝ)|=(4300891681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17203569/40000000 : ℝ)|^1043 ≤ (16342945610083/50000000000000 : ℝ)^787
        have hw : |(17203569/40000000 : ℝ)|=(17203569/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_12 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-32649413/156250000 : ℝ)*x 0 + (5439477483/10000000000 : ℝ)*x 1 + (1318304059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32649413/156250000 : ℝ)^1043 ≤ (1255679914511/10000000000000 : ℝ)^787 := by
    have hnat : (32649413 : ℕ)^1043*10000000000000^787 ≤ 1255679914511^787*156250000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32649413 156250000 1255679914511 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439477483/10000000000 : ℝ)^1043 ≤ (22310416047063/50000000000000 : ℝ)^787 := by
    have hnat : (5439477483 : ℕ)^1043*50000000000000^787 ≤ 22310416047063^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439477483 10000000000 22310416047063 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318304059/2500000000 : ℝ)^1043 ≤ (21411184370627/50000000000000 : ℝ)^787 := by
    have hnat : (1318304059 : ℕ)^1043*50000000000000^787 ≤ 21411184370627^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318304059 2500000000 21411184370627 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32649413/156250000 : ℝ), (5439477483/10000000000 : ℝ), (1318304059/2500000000 : ℝ)] ![(1255679914511/10000000000000 : ℝ), (22310416047063/50000000000000 : ℝ), (21411184370627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32649413/156250000 : ℝ)|^1043 ≤ (1255679914511/10000000000000 : ℝ)^787
        have hw : |(-32649413/156250000 : ℝ)|=(32649413/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439477483/10000000000 : ℝ)|^1043 ≤ (22310416047063/50000000000000 : ℝ)^787
        have hw : |(5439477483/10000000000 : ℝ)|=(5439477483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318304059/2500000000 : ℝ)|^1043 ≤ (21411184370627/50000000000000 : ℝ)^787
        have hw : |(1318304059/2500000000 : ℝ)|=(1318304059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_13 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684397263/5000000000 : ℝ)*x 0 + (-1092570627/5000000000 : ℝ)*x 1 + (5273216533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684397263/5000000000 : ℝ)^1043 ≤ (10963507525789/25000000000000 : ℝ)^787 := by
    have hnat : (2684397263 : ℕ)^1043*25000000000000^787 ≤ 10963507525789^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684397263 5000000000 10963507525789 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092570627/5000000000 : ℝ)^1043 ≤ (1332359795041/10000000000000 : ℝ)^787 := by
    have hnat : (1092570627 : ℕ)^1043*10000000000000^787 ≤ 1332359795041^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092570627 5000000000 1332359795041 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273216533/10000000000 : ℝ)^1043 ≤ (8564474387531/20000000000000 : ℝ)^787 := by
    have hnat : (5273216533 : ℕ)^1043*20000000000000^787 ≤ 8564474387531^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273216533 10000000000 8564474387531 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684397263/5000000000 : ℝ), (-1092570627/5000000000 : ℝ), (5273216533/10000000000 : ℝ)] ![(10963507525789/25000000000000 : ℝ), (1332359795041/10000000000000 : ℝ), (8564474387531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684397263/5000000000 : ℝ)|^1043 ≤ (10963507525789/25000000000000 : ℝ)^787
        have hw : |(2684397263/5000000000 : ℝ)|=(2684397263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092570627/5000000000 : ℝ)|^1043 ≤ (1332359795041/10000000000000 : ℝ)^787
        have hw : |(-1092570627/5000000000 : ℝ)|=(1092570627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273216533/10000000000 : ℝ)|^1043 ≤ (8564474387531/20000000000000 : ℝ)^787
        have hw : |(5273216533/10000000000 : ℝ)|=(5273216533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_14 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368794449/10000000000 : ℝ)*x 0 + (5273216807/10000000000 : ℝ)*x 1 + (-2185140991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368794449/10000000000 : ℝ)^1043 ≤ (43854029269603/100000000000000 : ℝ)^787 := by
    have hnat : (5368794449 : ℕ)^1043*100000000000000^787 ≤ 43854029269603^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368794449 10000000000 43854029269603 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273216807/10000000000 : ℝ)^1043 ≤ (21411187443261/50000000000000 : ℝ)^787 := by
    have hnat : (5273216807 : ℕ)^1043*50000000000000^787 ≤ 21411187443261^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273216807 10000000000 21411187443261 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185140991/10000000000 : ℝ)^1043 ≤ (13323595825173/100000000000000 : ℝ)^787 := by
    have hnat : (2185140991 : ℕ)^1043*100000000000000^787 ≤ 13323595825173^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185140991 10000000000 13323595825173 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368794449/10000000000 : ℝ), (5273216807/10000000000 : ℝ), (-2185140991/10000000000 : ℝ)] ![(43854029269603/100000000000000 : ℝ), (21411187443261/50000000000000 : ℝ), (13323595825173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368794449/10000000000 : ℝ)|^1043 ≤ (43854029269603/100000000000000 : ℝ)^787
        have hw : |(5368794449/10000000000 : ℝ)|=(5368794449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273216807/10000000000 : ℝ)|^1043 ≤ (21411187443261/50000000000000 : ℝ)^787
        have hw : |(5273216807/10000000000 : ℝ)|=(5273216807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185140991/10000000000 : ℝ)|^1043 ≤ (13323595825173/100000000000000 : ℝ)^787
        have hw : |(-2185140991/10000000000 : ℝ)|=(2185140991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_box_15 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1059283801/2500000000 : ℝ)*x 0 + (553563167/1250000000 : ℝ)*x 1 + (2214252259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059283801/2500000000 : ℝ)^1043 ≤ (32045290173913/100000000000000 : ℝ)^787 := by
    have hnat : (1059283801 : ℕ)^1043*100000000000000^787 ≤ 32045290173913^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059283801 2500000000 32045290173913 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553563167/1250000000 : ℝ)^1043 ≤ (3397735906333/10000000000000 : ℝ)^787 := by
    have hnat : (553563167 : ℕ)^1043*10000000000000^787 ≤ 3397735906333^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553563167 1250000000 3397735906333 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214252259/5000000000 : ℝ)^1043 ≤ (16988675372891/50000000000000 : ℝ)^787 := by
    have hnat : (2214252259 : ℕ)^1043*50000000000000^787 ≤ 16988675372891^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214252259 5000000000 16988675372891 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059283801/2500000000 : ℝ), (553563167/1250000000 : ℝ), (2214252259/5000000000 : ℝ)] ![(32045290173913/100000000000000 : ℝ), (3397735906333/10000000000000 : ℝ), (16988675372891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059283801/2500000000 : ℝ)|^1043 ≤ (32045290173913/100000000000000 : ℝ)^787
        have hw : |(1059283801/2500000000 : ℝ)|=(1059283801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553563167/1250000000 : ℝ)|^1043 ≤ (3397735906333/10000000000000 : ℝ)^787
        have hw : |(553563167/1250000000 : ℝ)|=(553563167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2214252259/5000000000 : ℝ)|^1043 ≤ (16988675372891/50000000000000 : ℝ)^787
        have hw : |(2214252259/5000000000 : ℝ)|=(2214252259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7779/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29653/50000 : ℝ) ∧ (19959/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10393/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5683/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (14216743120564069/100000000000000000000 : ℝ) := by
    have hpowers : (5683/50000 : ℝ)^8343 ≤ (14216743120564069/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5683 : ℕ)^8343*100000000000000000000^2048 ≤ 14216743120564069^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 50000 14216743120564069 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/50000 : ℝ)) (X := (14216743120564069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (8343/2048 : ℝ) ≤ (2109214822543797/6250000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^8343 ≤ (2109214822543797/6250000000000000000 : ℝ)^2048 := by
      have hnat : (14053 : ℕ)^8343*6250000000000000000^2048 ≤ 2109214822543797^2048*100000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 2109214822543797 6250000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (2109214822543797/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014216743120564069/50000000000000000000 : ℝ) ≤ (5000348948426253/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50014216743120564069/50000000000000000000 : ℝ)^2048 ≤ (5000348948426253/5000000000000000 : ℝ)^8343 := by
      have hnat : (50014216743120564069 : ℕ)^2048*5000000000000000^8343 ≤ 5000348948426253^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014216743120564069 50000000000000000000 5000348948426253 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348948426253/5000000000000000 : ℝ)) (X := (50014216743120564069/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047964180281264821/100000000000000000000 : ℝ) ≤ (10001177188916299/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (100047964180281264821/100000000000000000000 : ℝ)^2048 ≤ (10001177188916299/10000000000000000 : ℝ)^8343 := by
      have hnat : (100047964180281264821 : ℕ)^2048*10000000000000000^8343 ≤ 10001177188916299^8343*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047964180281264821 100000000000000000000 10001177188916299 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177188916299/10000000000000000 : ℝ)) (X := (100047964180281264821/100000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127109214822543797/3125000000000000000 : ℝ) ≤ (2500414120245023/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (3127109214822543797/3125000000000000000 : ℝ)^2048 ≤ (2500414120245023/2500000000000000 : ℝ)^8343 := by
      have hnat : (3127109214822543797 : ℕ)^2048*2500000000000000^8343 ≤ 2500414120245023^8343*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127109214822543797 3125000000000000000 2500414120245023 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414120245023/2500000000000000 : ℝ)) (X := (3127109214822543797/3125000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14216743120564069/100000000000000000000 : ℝ) ≤ ((13430489990824270573/13435000000000000000 : ℝ)+2*(479292063793/268700000000000 : ℝ)*(5683/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (13430489990824270573/13435000000000000000 : ℝ)+2*(479292063793/268700000000000 : ℝ)*(5683/50000 : ℝ)=(5000348948426253/5000000000000000 : ℝ) by norm_num, show 1+2*(14216743120564069/100000000000000000000 : ℝ)=(50014216743120564069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2109214822543797/6250000000000000000 : ℝ)+(14216743120564069/100000000000000000000 : ℝ) ≤ ((13430489990824270573/13435000000000000000 : ℝ)+(479292063793/268700000000000 : ℝ)*((14053/100000 : ℝ)+(5683/50000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (13430489990824270573/13435000000000000000 : ℝ)+(479292063793/268700000000000 : ℝ)*((14053/100000 : ℝ)+(5683/50000 : ℝ))=(10001177188916299/10000000000000000 : ℝ) by norm_num, show 1+(2109214822543797/6250000000000000000 : ℝ)+(14216743120564069/100000000000000000000 : ℝ)=(100047964180281264821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2109214822543797/6250000000000000000 : ℝ) ≤ ((13430489990824270573/13435000000000000000 : ℝ)+2*(479292063793/268700000000000 : ℝ)*(14053/100000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (13430489990824270573/13435000000000000000 : ℝ)+2*(479292063793/268700000000000 : ℝ)*(14053/100000 : ℝ)=(2500414120245023/2500000000000000 : ℝ) by norm_num, show 1+2*(2109214822543797/6250000000000000000 : ℝ)=(3127109214822543797/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13430489990824270573/13435000000000000000 : ℝ)*(X 1 0+X 2 0)+(479292063793/268700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13430489990824270573/13435000000000000000 : ℝ)) (alpha := (479292063793/268700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13430489990824270573/13435000000000000000 : ℝ)*(X 0 1+X 2 1)+(479292063793/268700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13430489990824270573/13435000000000000000 : ℝ)) (alpha := (479292063793/268700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13430489990824270573/13435000000000000000 : ℝ)*(X 0 2+X 1 2)+(479292063793/268700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13430489990824270573/13435000000000000000 : ℝ)) (alpha := (479292063793/268700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2036006487/10000000000 : ℝ)*X 0 0+(5376176801/10000000000 : ℝ)*X 0 1+(1075235479/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059213883/2000000000 : ℝ)*X 1 0+(-2144668069/10000000000 : ℝ)*X 1 1+(1075235509/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((105921401/200000000 : ℝ)*X 2 0+(1344044287/2500000000 : ℝ)*X 2 1+(-268083469/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4470849897/10000000000 : ℝ)*X 0 0+(67371731/156250000 : ℝ)*X 0 1+(4311790397/10000000000 : ℝ)*X 0 2+(4470849897/10000000000 : ℝ)*X 1 0+(67371731/156250000 : ℝ)*X 1 1+(4311790397/10000000000 : ℝ)*X 1 2+(4470849897/10000000000 : ℝ)*X 2 0+(67371731/156250000 : ℝ)*X 2 1+(4311790397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1145282769/5000000000 : ℝ)*X 0 0+(5281257869/10000000000 : ℝ)*X 0 1+(2640629309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670389537/1250000000 : ℝ)*X 1 0+(-2182033249/10000000000 : ℝ)*X 1 1+(5281258133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681558583/5000000000 : ℝ)*X 2 0+(1320314519/2500000000 : ℝ)*X 2 1+(-2182032159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127801907/5000000000 : ℝ)*X 0 0+(883878617/2000000000 : ℝ)*X 0 1+(88387853/200000000 : ℝ)*X 0 2+(2127801907/5000000000 : ℝ)*X 1 0+(883878617/2000000000 : ℝ)*X 1 1+(88387853/200000000 : ℝ)*X 1 2+(2127801907/5000000000 : ℝ)*X 2 0+(883878617/2000000000 : ℝ)*X 2 1+(88387853/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-44746457/200000000 : ℝ)*X 0 0+(5216687123/10000000000 : ℝ)*X 0 1+(5385785427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289279501/10000000000 : ℝ)*X 1 0+(-1070408277/5000000000 : ℝ)*X 1 1+(2692892829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057855733/2000000000 : ℝ)*X 2 0+(2692893179/5000000000 : ℝ)*X 2 1+(-214081673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4492366121/10000000000 : ℝ)*X 0 0+(4300891681/10000000000 : ℝ)*X 0 1+(17203569/40000000 : ℝ)*X 0 2+(4492366121/10000000000 : ℝ)*X 1 0+(4300891681/10000000000 : ℝ)*X 1 1+(17203569/40000000 : ℝ)*X 1 2+(4492366121/10000000000 : ℝ)*X 2 0+(4300891681/10000000000 : ℝ)*X 2 1+(17203569/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-32649413/156250000 : ℝ)*X 0 0+(5439477483/10000000000 : ℝ)*X 0 1+(1318304059/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684397263/5000000000 : ℝ)*X 1 0+(-1092570627/5000000000 : ℝ)*X 1 1+(5273216533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368794449/10000000000 : ℝ)*X 2 0+(5273216807/10000000000 : ℝ)*X 2 1+(-2185140991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1059283801/2500000000 : ℝ)*X 0 0+(553563167/1250000000 : ℝ)*X 0 1+(2214252259/5000000000 : ℝ)*X 0 2+(1059283801/2500000000 : ℝ)*X 1 0+(553563167/1250000000 : ℝ)*X 1 1+(2214252259/5000000000 : ℝ)*X 1 2+(1059283801/2500000000 : ℝ)*X 2 0+(553563167/1250000000 : ℝ)*X 2 1+(2214252259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7779/12500 : ℝ) ≤ (-209013565199087933292574732982961/335875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52333573/50000000000000 : ℝ)*(upper0) + (662841091/100000000000000 : ℝ)*(lower2) + (1924297/800000000000 : ℝ)*(lower3) + (1964143802821281/50000000000000 : ℝ)*(major0) + (1964143802821281/50000000000000 : ℝ)*(major1) + (3928287605642563/100000000000000 : ℝ)*(major2) + (1416040909/25000000000000 : ℝ)*(sp1) + (1179187741/100000000000000 : ℝ)*(sp3) + (328269979628199/6250000000000 : ℝ)*(sp4) + (82067465545041/1562500000000 : ℝ)*(sp5) + (5252027696971547/100000000000000 : ℝ)*(sp6) + (1312496881374783/50000000000000 : ℝ)*(sp7) + (3784995077/100000000000000 : ℝ)*(sp8) + (295762074713/100000000000000 : ℝ)*(sp14) + (1312497470968653/50000000000000 : ℝ)*(f.failure) + (5252323459046261/100000000000000 : ℝ)*(f.sum) + (8841184657841/5374000000000000000000000000 : ℝ)*base66 + (1749561628463810987/671750000000000000000000000000000 : ℝ)*base68 + (4314981902637501401/1343500000000000000000000000000000 : ℝ)*base70 + (7215726147635810987/671750000000000000000000000000000 : ℝ)*base72 + (73303764978869/5374000000000000000000000000 : ℝ)*base73 + (7235506741148998599/1343500000000000000000000000000000 : ℝ)*base75 + (9545588739896885987/671750000000000000000000000000000 : ℝ)*base78 + (22620156632578364013/671750000000000000000000000000000 : ℝ)*base79 + (101210377861969/13435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (893049/250000000000000000000 : ℝ)*base90 + (893049/250000000000000000000 : ℝ)*base92 + (3393049/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29653/50000 : ℝ) ≤ (199200852548497253579898983188281/335875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4399183/10000000000000 : ℝ)*(lower0) + (29347499/20000000000000 : ℝ)*(lower3) + (13404363/5000000000000 : ℝ)*(upper4) + (499077012283861/12500000000000 : ℝ)*(major0) + (499077012283861/12500000000000 : ℝ)*(major1) + (399261609827089/10000000000000 : ℝ)*(major2) + (5297481137405221/100000000000000 : ℝ)*(sp0) + (2648728627028421/50000000000000 : ℝ)*(sp1) + (2648733720715679/50000000000000 : ℝ)*(sp2) + (20843518618147/781250000000 : ℝ)*(sp3) + (12252314201/50000000000000 : ℝ)*(sp5) + (7158626943/50000000000000 : ℝ)*(sp6) + (5355363453/50000000000000 : ℝ)*(sp7) + (621280023/100000000000000 : ℝ)*(sp12) + (1333990546924861/50000000000000 : ℝ)*(f.failure) + (1324370439671311/25000000000000 : ℝ)*(f.sum) + (51643495823389/6717500000000000000000000000 : ℝ)*base66 + (1191023460775565147/167937500000000000000000000000000 : ℝ)*base68 + (2597892204770621997/134350000000000000000000000000000 : ℝ)*base69 + (2565730106471690147/167937500000000000000000000000000 : ℝ)*base72 + (254819551965247/13435000000000000000000000000 : ℝ)*base73 + (1813547012177071997/134350000000000000000000000000000 : ℝ)*base75 + (1638510800056477647/167937500000000000000000000000000 : ℝ)*base78 + (4068264298393897353/167937500000000000000000000000000 : ℝ)*base79 + (5994199082143/6717500000000000000000000000 : ℝ)*base82 + (3912087/250000000000000000000 : ℝ)*base89 + (3912087/250000000000000000000 : ℝ)*base91 + (1087913/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19959/25000 : ℝ) ≤ (268156958593003608206314932534873/335875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7873137/100000000000000 : ℝ)*(upper1) + (363374929/100000000000000 : ℝ)*(upper2) + (175039/20000000000000 : ℝ)*(lower5) + (4460476323861367/100000000000000 : ℝ)*(major0) + (4460476323861367/100000000000000 : ℝ)*(major1) + (557559540482671/12500000000000 : ℝ)*(major2) + (30635692337/10000000000000 : ℝ)*(sp1) + (249599950501/50000000000000 : ℝ)*(sp2) + (7790775623/5000000000000 : ℝ)*(sp3) + (716902689/5000000000000 : ℝ)*(sp4) + (5913706761770081/100000000000000 : ℝ)*(sp8) + (591341474290049/10000000000000 : ℝ)*(sp9) + (5913221899922859/100000000000000 : ℝ)*(sp10) + (2980462958924747/100000000000000 : ℝ)*(sp11) + (1490309387218603/50000000000000 : ℝ)*(f.failure) + (5913721099823861/100000000000000 : ℝ)*(f.sum) + (34806840763587/5374000000000000000000000000 : ℝ)*base66 + (13358686149664146709/1343500000000000000000000000000000 : ℝ)*base68 + (119693263269496733/167937500000000000000000000000000 : ℝ)*base69 + (12210849347653646709/1343500000000000000000000000000000 : ℝ)*base72 + (45917701532253/5374000000000000000000000000 : ℝ)*base73 + (1475043494314315767/167937500000000000000000000000000 : ℝ)*base76 + (29050206788675796709/1343500000000000000000000000000000 : ℝ)*base78 + (32271855062876296709/1343500000000000000000000000000000 : ℝ)*base80 + (44944697039229/13435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1233601/250000000000000000000 : ℝ)*base89 + (1233601/250000000000000000000 : ℝ)*base91 + (1266399/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-10393/12500 : ℝ) ≤ (-558506305917818721611961692776821/671750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395308791/100000000000000 : ℝ)*(lower0) + (12435783/100000000000000 : ℝ)*(lower1) + (67497389/25000000000000 : ℝ)*(upper5) + (4495462760083341/100000000000000 : ℝ)*(major0) + (4495462760083341/100000000000000 : ℝ)*(major1) + (2247731380041671/50000000000000 : ℝ)*(major2) + (3349774029/100000000000000 : ℝ)*(sp4) + (40780967249/50000000000000 : ℝ)*(sp5) + (8328999333/4000000000000 : ℝ)*(sp7) + (20351386271/100000000000000 : ℝ)*(sp8) + (6014618096092343/100000000000000 : ℝ)*(sp12) + (3007280117659073/50000000000000 : ℝ)*(sp13) + (1503660449313161/25000000000000 : ℝ)*(sp14) + (300378949400651/10000000000000 : ℝ)*(sp15) + (1501998859494917/50000000000000 : ℝ)*(f.failure) + (1503660449313161/25000000000000 : ℝ)*(f.sum) + (117161338125321/26870000000000000000000000000 : ℝ)*base66 + (74352291621246124393/1343500000000000000000000000000000 : ℝ)*base67 + (234097486440377517/671750000000000000000000000000000 : ℝ)*base70 + (5483311762414875607/1343500000000000000000000000000000 : ℝ)*base72 + (798675488302489/26870000000000000000000000000 : ℝ)*base73 + (5874464856695872483/671750000000000000000000000000000 : ℝ)*base75 + (12138960238616525607/1343500000000000000000000000000000 : ℝ)*base78 + (37956032347411025607/1343500000000000000000000000000000 : ℝ)*base80 + (16430103831103/13435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (620239/250000000000000000000 : ℝ)*base89 + (620239/250000000000000000000 : ℝ)*base91 + (1879761/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1151_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29653/50000 : ℝ) else (19959/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10393/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1151_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1151_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29653/50000 : ℝ) else (19959/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10393/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1151_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1151_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1151_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29653/50000 : ℝ) else (19959/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10393/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
