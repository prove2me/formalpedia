-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:07.679706+00:00
-- url     : https://prove2.me/submissions/81d89ccb-7960-42b9-8415-c8d552caab76

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
theorem support_rectangle_w1138_s3_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164955989/10000000000 : ℝ)*x 0 + (5429588813/10000000000 : ℝ)*x 1 + (5231708429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164955989/10000000000 : ℝ)^8331 ≤ (657359225831/5000000000000 : ℝ)^6283 := by
    have hnat : (2164955989 : ℕ)^8331*5000000000000^6283 ≤ 657359225831^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164955989 10000000000 657359225831 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429588813/10000000000 : ℝ)^8331 ≤ (44495066028259/100000000000000 : ℝ)^6283 := by
    have hnat : (5429588813 : ℕ)^8331*100000000000000^6283 ≤ 44495066028259^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429588813 10000000000 44495066028259 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231708429/10000000000 : ℝ)^8331 ≤ (529471867917/1250000000000 : ℝ)^6283 := by
    have hnat : (5231708429 : ℕ)^8331*1250000000000^6283 ≤ 529471867917^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231708429 10000000000 529471867917 1250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164955989/10000000000 : ℝ), (5429588813/10000000000 : ℝ), (5231708429/10000000000 : ℝ)] ![(657359225831/5000000000000 : ℝ), (44495066028259/100000000000000 : ℝ), (529471867917/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164955989/10000000000 : ℝ)|^8331 ≤ (657359225831/5000000000000 : ℝ)^6283
        have hw : |(-2164955989/10000000000 : ℝ)|=(2164955989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429588813/10000000000 : ℝ)|^8331 ≤ (44495066028259/100000000000000 : ℝ)^6283
        have hw : |(5429588813/10000000000 : ℝ)|=(5429588813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231708429/10000000000 : ℝ)|^8331 ≤ (529471867917/1250000000000 : ℝ)^6283
        have hw : |(5231708429/10000000000 : ℝ)|=(5231708429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338472347/2500000000 : ℝ)*x 0 + (-566528637/2500000000 : ℝ)*x 1 + (130792707/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338472347/2500000000 : ℝ)^8331 ≤ (43674381021837/100000000000000 : ℝ)^6283 := by
    have hnat : (1338472347 : ℕ)^8331*100000000000000^6283 ≤ 43674381021837^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338472347 2500000000 43674381021837 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566528637/2500000000 : ℝ)^8331 ≤ (13967871115787/100000000000000 : ℝ)^6283 := by
    have hnat : (566528637 : ℕ)^8331*100000000000000^6283 ≤ 13967871115787^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566528637 2500000000 13967871115787 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130792707/250000000 : ℝ)^8331 ≤ (42357747833781/100000000000000 : ℝ)^6283 := by
    have hnat : (130792707 : ℕ)^8331*100000000000000^6283 ≤ 42357747833781^6283*250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130792707 250000000 42357747833781 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338472347/2500000000 : ℝ), (-566528637/2500000000 : ℝ), (130792707/250000000 : ℝ)] ![(43674381021837/100000000000000 : ℝ), (13967871115787/100000000000000 : ℝ), (42357747833781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338472347/2500000000 : ℝ)|^8331 ≤ (43674381021837/100000000000000 : ℝ)^6283
        have hw : |(1338472347/2500000000 : ℝ)|=(1338472347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566528637/2500000000 : ℝ)|^8331 ≤ (13967871115787/100000000000000 : ℝ)^6283
        have hw : |(-566528637/2500000000 : ℝ)|=(566528637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130792707/250000000 : ℝ)|^8331 ≤ (42357747833781/100000000000000 : ℝ)^6283
        have hw : |(130792707/250000000 : ℝ)|=(130792707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353889473/10000000000 : ℝ)*x 0 + (5231708367/10000000000 : ℝ)*x 1 + (-2266114323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353889473/10000000000 : ℝ)^8331 ≤ (43674381941241/100000000000000 : ℝ)^6283 := by
    have hnat : (5353889473 : ℕ)^8331*100000000000000^6283 ≤ 43674381941241^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353889473 10000000000 43674381941241 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231708367/10000000000 : ℝ)^8331 ≤ (10589437191941/25000000000000 : ℝ)^6283 := by
    have hnat : (5231708367 : ℕ)^8331*25000000000000^6283 ≤ 10589437191941^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231708367 10000000000 10589437191941 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266114323/10000000000 : ℝ)^8331 ≤ (22348590843/160000000000 : ℝ)^6283 := by
    have hnat : (2266114323 : ℕ)^8331*160000000000^6283 ≤ 22348590843^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266114323 10000000000 22348590843 160000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353889473/10000000000 : ℝ), (5231708367/10000000000 : ℝ), (-2266114323/10000000000 : ℝ)] ![(43674381941241/100000000000000 : ℝ), (10589437191941/25000000000000 : ℝ), (22348590843/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353889473/10000000000 : ℝ)|^8331 ≤ (43674381941241/100000000000000 : ℝ)^6283
        have hw : |(5353889473/10000000000 : ℝ)|=(5353889473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231708367/10000000000 : ℝ)|^8331 ≤ (10589437191941/25000000000000 : ℝ)^6283
        have hw : |(5231708367/10000000000 : ℝ)|=(5231708367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266114323/10000000000 : ℝ)|^8331 ≤ (22348590843/160000000000 : ℝ)^6283
        have hw : |(-2266114323/10000000000 : ℝ)|=(2266114323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362953821/10000000000 : ℝ)*x 0 + (4170678993/10000000000 : ℝ)*x 1 + (570505969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362953821/10000000000 : ℝ)^8331 ≤ (8323460016077/25000000000000 : ℝ)^6283 := by
    have hnat : (4362953821 : ℕ)^8331*25000000000000^6283 ≤ 8323460016077^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362953821 10000000000 8323460016077 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170678993/10000000000 : ℝ)^8331 ≤ (15681217177789/50000000000000 : ℝ)^6283 := by
    have hnat : (4170678993 : ℕ)^8331*50000000000000^6283 ≤ 15681217177789^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170678993 10000000000 15681217177789 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570505969/1250000000 : ℝ)^8331 ≤ (17671862782993/50000000000000 : ℝ)^6283 := by
    have hnat : (570505969 : ℕ)^8331*50000000000000^6283 ≤ 17671862782993^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570505969 1250000000 17671862782993 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362953821/10000000000 : ℝ), (4170678993/10000000000 : ℝ), (570505969/1250000000 : ℝ)] ![(8323460016077/25000000000000 : ℝ), (15681217177789/50000000000000 : ℝ), (17671862782993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362953821/10000000000 : ℝ)|^8331 ≤ (8323460016077/25000000000000 : ℝ)^6283
        have hw : |(4362953821/10000000000 : ℝ)|=(4362953821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170678993/10000000000 : ℝ)|^8331 ≤ (15681217177789/50000000000000 : ℝ)^6283
        have hw : |(4170678993/10000000000 : ℝ)|=(4170678993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570505969/1250000000 : ℝ)|^8331 ≤ (17671862782993/50000000000000 : ℝ)^6283
        have hw : |(570505969/1250000000 : ℝ)|=(570505969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135310891/625000000 : ℝ)*x 0 + (654059771/1250000000 : ℝ)*x 1 + (5428814761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135310891/625000000 : ℝ)^8331 ≤ (13147331606091/100000000000000 : ℝ)^6283 := by
    have hnat : (135310891 : ℕ)^8331*100000000000000^6283 ≤ 13147331606091^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135310891 625000000 13147331606091 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654059771/1250000000 : ℝ)^8331 ≤ (5295751638773/12500000000000 : ℝ)^6283 := by
    have hnat : (654059771 : ℕ)^8331*12500000000000^6283 ≤ 5295751638773^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654059771 1250000000 5295751638773 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428814761/10000000000 : ℝ)^8331 ≤ (22243327636121/50000000000000 : ℝ)^6283 := by
    have hnat : (5428814761 : ℕ)^8331*50000000000000^6283 ≤ 22243327636121^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428814761 10000000000 22243327636121 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135310891/625000000 : ℝ), (654059771/1250000000 : ℝ), (5428814761/10000000000 : ℝ)] ![(13147331606091/100000000000000 : ℝ), (5295751638773/12500000000000 : ℝ), (22243327636121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135310891/625000000 : ℝ)|^8331 ≤ (13147331606091/100000000000000 : ℝ)^6283
        have hw : |(-135310891/625000000 : ℝ)|=(135310891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654059771/1250000000 : ℝ)|^8331 ≤ (5295751638773/12500000000000 : ℝ)^6283
        have hw : |(654059771/1250000000 : ℝ)|=(654059771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428814761/10000000000 : ℝ)|^8331 ≤ (22243327636121/50000000000000 : ℝ)^6283
        have hw : |(5428814761/10000000000 : ℝ)|=(5428814761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060754367/2000000000 : ℝ)*x 0 + (-413801711/2000000000 : ℝ)*x 1 + (1357203627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060754367/2000000000 : ℝ)^8331 ≤ (43133112449733/100000000000000 : ℝ)^6283 := by
    have hnat : (1060754367 : ℕ)^8331*100000000000000^6283 ≤ 43133112449733^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060754367 2000000000 43133112449733 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413801711/2000000000 : ℝ)^8331 ≤ (12380235007657/100000000000000 : ℝ)^6283 := by
    have hnat : (413801711 : ℕ)^8331*100000000000000^6283 ≤ 12380235007657^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413801711 2000000000 12380235007657 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357203627/2500000000 : ℝ)^8331 ≤ (44486652523239/100000000000000 : ℝ)^6283 := by
    have hnat : (1357203627 : ℕ)^8331*100000000000000^6283 ≤ 44486652523239^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357203627 2500000000 44486652523239 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060754367/2000000000 : ℝ), (-413801711/2000000000 : ℝ), (1357203627/2500000000 : ℝ)] ![(43133112449733/100000000000000 : ℝ), (12380235007657/100000000000000 : ℝ), (44486652523239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060754367/2000000000 : ℝ)|^8331 ≤ (43133112449733/100000000000000 : ℝ)^6283
        have hw : |(1060754367/2000000000 : ℝ)|=(1060754367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413801711/2000000000 : ℝ)|^8331 ≤ (12380235007657/100000000000000 : ℝ)^6283
        have hw : |(-413801711/2000000000 : ℝ)|=(413801711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357203627/2500000000 : ℝ)|^8331 ≤ (44486652523239/100000000000000 : ℝ)^6283
        have hw : |(1357203627/2500000000 : ℝ)|=(1357203627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303772501/10000000000 : ℝ)*x 0 + (1357203509/2500000000 : ℝ)*x 1 + (-2069008297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303772501/10000000000 : ℝ)^8331 ≤ (43133119631483/100000000000000 : ℝ)^6283 := by
    have hnat : (5303772501 : ℕ)^8331*100000000000000^6283 ≤ 43133119631483^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303772501 10000000000 43133119631483 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357203509/2500000000 : ℝ)^8331 ≤ (44486647394663/100000000000000 : ℝ)^6283 := by
    have hnat : (1357203509 : ℕ)^8331*100000000000000^6283 ≤ 44486647394663^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357203509 2500000000 44486647394663 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069008297/10000000000 : ℝ)^8331 ≤ (12380232960663/100000000000000 : ℝ)^6283 := by
    have hnat : (2069008297 : ℕ)^8331*100000000000000^6283 ≤ 12380232960663^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069008297 10000000000 12380232960663 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303772501/10000000000 : ℝ), (1357203509/2500000000 : ℝ), (-2069008297/10000000000 : ℝ)] ![(43133119631483/100000000000000 : ℝ), (44486647394663/100000000000000 : ℝ), (12380232960663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303772501/10000000000 : ℝ)|^8331 ≤ (43133119631483/100000000000000 : ℝ)^6283
        have hw : |(5303772501/10000000000 : ℝ)|=(5303772501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357203509/2500000000 : ℝ)|^8331 ≤ (44486647394663/100000000000000 : ℝ)^6283
        have hw : |(1357203509/2500000000 : ℝ)|=(1357203509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069008297/10000000000 : ℝ)|^8331 ≤ (12380232960663/100000000000000 : ℝ)^6283
        have hw : |(-2069008297/10000000000 : ℝ)|=(2069008297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s3_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362989897/10000000000 : ℝ)*x 0 + (91250353/200000000 : ℝ)*x 1 + (2086108963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362989897/10000000000 : ℝ)^8331 ≤ (16647102548731/50000000000000 : ℝ)^6283 := by
    have hnat : (4362989897 : ℕ)^8331*50000000000000^6283 ≤ 16647102548731^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362989897 10000000000 16647102548731 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91250353/200000000 : ℝ)^8331 ≤ (35328015107031/100000000000000 : ℝ)^6283 := by
    have hnat : (91250353 : ℕ)^8331*100000000000000^6283 ≤ 35328015107031^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91250353 200000000 35328015107031 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086108963/5000000000 : ℝ)^8331 ≤ (1255111191197/4000000000000 : ℝ)^6283 := by
    have hnat : (2086108963 : ℕ)^8331*4000000000000^6283 ≤ 1255111191197^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086108963 5000000000 1255111191197 4000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362989897/10000000000 : ℝ), (91250353/200000000 : ℝ), (2086108963/5000000000 : ℝ)] ![(16647102548731/50000000000000 : ℝ), (35328015107031/100000000000000 : ℝ), (1255111191197/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362989897/10000000000 : ℝ)|^8331 ≤ (16647102548731/50000000000000 : ℝ)^6283
        have hw : |(4362989897/10000000000 : ℝ)|=(4362989897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91250353/200000000 : ℝ)|^8331 ≤ (35328015107031/100000000000000 : ℝ)^6283
        have hw : |(91250353/200000000 : ℝ)|=(91250353/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086108963/5000000000 : ℝ)|^8331 ≤ (1255111191197/4000000000000 : ℝ)^6283
        have hw : |(2086108963/5000000000 : ℝ)|=(2086108963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10623/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1481/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8257/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8257/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8257/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8257/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8257/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8257/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/25000 : ℝ) ^ (4165/1024 : ℝ) ≤ (5710586238658133/100000000000000000000 : ℝ) := by
    have hpowers : (2263/25000 : ℝ)^4165 ≤ (5710586238658133/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2263 : ℕ)^4165*100000000000000000000^1024 ≤ 5710586238658133^1024*25000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 25000 5710586238658133 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/25000 : ℝ)) (X := (5710586238658133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8257/50000 : ℝ) ^ (4165/1024 : ℝ) ≤ (526982016397403/800000000000000000 : ℝ) := by
    have hpowers : (8257/50000 : ℝ)^4165 ≤ (526982016397403/800000000000000000 : ℝ)^1024 := by
      have hnat : (8257 : ℕ)^4165*800000000000000000^1024 ≤ 526982016397403^1024*50000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8257 50000 526982016397403 800000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8257/50000 : ℝ)) (X := (526982016397403/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005710586238658133/50000000000000000000 : ℝ) ≤ (5000140393481183/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50005710586238658133/50000000000000000000 : ℝ)^1024 ≤ (5000140393481183/5000000000000000 : ℝ)^4165 := by
      have hnat : (50005710586238658133 : ℕ)^1024*5000000000000000^4165 ≤ 5000140393481183^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005710586238658133 50000000000000000000 5000140393481183 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140393481183/5000000000000000 : ℝ)) (X := (50005710586238658133/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25017895834572083377/25000000000000000000 : ℝ) ≤ (2500439865313299/2500000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (25017895834572083377/25000000000000000000 : ℝ)^1024 ≤ (2500439865313299/2500000000000000 : ℝ)^4165 := by
      have hnat : (25017895834572083377 : ℕ)^1024*2500000000000000^4165 ≤ 2500439865313299^4165*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017895834572083377 25000000000000000000 2500439865313299 2500000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500439865313299/2500000000000000 : ℝ)) (X := (25017895834572083377/25000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400526982016397403/400000000000000000 : ℝ) ≤ (5001619067772013/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (400526982016397403/400000000000000000 : ℝ)^1024 ≤ (5001619067772013/5000000000000000 : ℝ)^4165 := by
      have hnat : (400526982016397403 : ℕ)^1024*5000000000000000^4165 ≤ 5001619067772013^4165*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400526982016397403 400000000000000000 5001619067772013 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001619067772013/5000000000000000 : ℝ)) (X := (400526982016397403/400000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5710586238658133/100000000000000000000 : ℝ) ≤ ((18648831328237997193/18655000000000000000 : ℝ)+2*(147867429083/74620000000000 : ℝ)*(2263/25000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (18648831328237997193/18655000000000000000 : ℝ)+2*(147867429083/74620000000000 : ℝ)*(2263/25000 : ℝ)=(5000140393481183/5000000000000000 : ℝ) by norm_num, show 1+2*(5710586238658133/100000000000000000000 : ℝ)=(50005710586238658133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(526982016397403/800000000000000000 : ℝ)+(5710586238658133/100000000000000000000 : ℝ) ≤ ((18648831328237997193/18655000000000000000 : ℝ)+(147867429083/74620000000000 : ℝ)*((8257/50000 : ℝ)+(2263/25000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (18648831328237997193/18655000000000000000 : ℝ)+(147867429083/74620000000000 : ℝ)*((8257/50000 : ℝ)+(2263/25000 : ℝ))=(2500439865313299/2500000000000000 : ℝ) by norm_num, show 1+(526982016397403/800000000000000000 : ℝ)+(5710586238658133/100000000000000000000 : ℝ)=(25017895834572083377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(526982016397403/800000000000000000 : ℝ) ≤ ((18648831328237997193/18655000000000000000 : ℝ)+2*(147867429083/74620000000000 : ℝ)*(8257/50000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (18648831328237997193/18655000000000000000 : ℝ)+2*(147867429083/74620000000000 : ℝ)*(8257/50000 : ℝ)=(5001619067772013/5000000000000000 : ℝ) by norm_num, show 1+2*(526982016397403/800000000000000000 : ℝ)=(400526982016397403/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18648831328237997193/18655000000000000000 : ℝ)*(X 1 0+X 2 0)+(147867429083/74620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (8257/50000 : ℝ)) (c := (18648831328237997193/18655000000000000000 : ℝ)) (alpha := (147867429083/74620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18648831328237997193/18655000000000000000 : ℝ)*(X 0 1+X 2 1)+(147867429083/74620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (8257/50000 : ℝ)) (c := (18648831328237997193/18655000000000000000 : ℝ)) (alpha := (147867429083/74620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18648831328237997193/18655000000000000000 : ℝ)*(X 0 2+X 1 2)+(147867429083/74620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (2263/25000 : ℝ)) (hi := (8257/50000 : ℝ)) (c := (18648831328237997193/18655000000000000000 : ℝ)) (alpha := (147867429083/74620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164955989/10000000000 : ℝ)*X 0 0+(5429588813/10000000000 : ℝ)*X 0 1+(5231708429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338472347/2500000000 : ℝ)*X 1 0+(-566528637/2500000000 : ℝ)*X 1 1+(130792707/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353889473/10000000000 : ℝ)*X 2 0+(5231708367/10000000000 : ℝ)*X 2 1+(-2266114323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362953821/10000000000 : ℝ)*X 0 0+(4170678993/10000000000 : ℝ)*X 0 1+(570505969/1250000000 : ℝ)*X 0 2+(4362953821/10000000000 : ℝ)*X 1 0+(4170678993/10000000000 : ℝ)*X 1 1+(570505969/1250000000 : ℝ)*X 1 2+(4362953821/10000000000 : ℝ)*X 2 0+(4170678993/10000000000 : ℝ)*X 2 1+(570505969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-135310891/625000000 : ℝ)*X 0 0+(654059771/1250000000 : ℝ)*X 0 1+(5428814761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060754367/2000000000 : ℝ)*X 1 0+(-413801711/2000000000 : ℝ)*X 1 1+(1357203627/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303772501/10000000000 : ℝ)*X 2 0+(1357203509/2500000000 : ℝ)*X 2 1+(-2069008297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362989897/10000000000 : ℝ)*X 0 0+(91250353/200000000 : ℝ)*X 0 1+(2086108963/5000000000 : ℝ)*X 0 2+(4362989897/10000000000 : ℝ)*X 1 0+(91250353/200000000 : ℝ)*X 1 1+(2086108963/5000000000 : ℝ)*X 1 2+(4362989897/10000000000 : ℝ)*X 2 0+(91250353/200000000 : ℝ)*X 2 1+(2086108963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1172578362774780201191446683/186550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1641287147/100000000000000 : ℝ)*(base19) + (1552865873/100000000000000 : ℝ)*(base23) + (18059097/20000000000000 : ℝ)*(lower2) + (84496273/100000000000000 : ℝ)*(upper3) + (104322713/50000000000000 : ℝ)*(upper5) + (759578560793023/20000000000000 : ℝ)*(major0) + (759578560793023/20000000000000 : ℝ)*(major1) + (759578560793023/20000000000000 : ℝ)*(major2) + (5053583180921403/100000000000000 : ℝ)*(sp0) + (5053613137729129/100000000000000 : ℝ)*(sp1) + (5053613226150403/100000000000000 : ℝ)*(sp2) + (1271078803810769/50000000000000 : ℝ)*(sp3) + (31598094873/100000000000000 : ℝ)*(sp4) + (2602354493/20000000000000 : ℝ)*(sp7) + (635542654848501/25000000000000 : ℝ)*(f.failure) + (1263403694754069/25000000000000 : ℝ)*(f.sum) + (29245708788757/3731000000000000000000000000 : ℝ)*base65 + (1292584021175534439/373100000000000000000000000000000 : ℝ)*base67 + (854430074226634439/373100000000000000000000000000000 : ℝ)*base69 + (1115432384804734439/373100000000000000000000000000000 : ℝ)*base71 + (16097183325593/3731000000000000000000000000 : ℝ)*base73 + (79835413201365561/373100000000000000000000000000000 : ℝ)*base76 + (3068676338857034439/373100000000000000000000000000000 : ℝ)*base77 + (5590821676338265561/373100000000000000000000000000000 : ℝ)*base80 + (4272487221369/1865500000000000000000000000 : ℝ)*base81 + (25542169/2500000000000000000000 : ℝ)*base89 + (25542169/2500000000000000000000 : ℝ)*base91 + (25542169/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5381753769093141783253119/2050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244631327/50000000000000 : ℝ)*(base19) + (1210306699/100000000000000 : ℝ)*(base23) + (693647/20000000000000 : ℝ)*(lower4) + (68108299/100000000000000 : ℝ)*(upper5) + (765543728252751/20000000000000 : ℝ)*(major0) + (765543728252751/20000000000000 : ℝ)*(major1) + (765543728252751/20000000000000 : ℝ)*(major2) + (656448697/100000000000000 : ℝ)*(sp0) + (341597231/6250000000000 : ℝ)*(sp1) + (6697856103/50000000000000 : ℝ)*(sp2) + (2546650796953241/50000000000000 : ℝ)*(sp4) + (5093296295536829/100000000000000 : ℝ)*(sp5) + (2546643822168137/50000000000000 : ℝ)*(sp6) + (40033358510377/1562500000000 : ℝ)*(sp7) + (40033358510377/1562500000000 : ℝ)*(f.failure) + (2546651125177589/50000000000000 : ℝ)*(f.sum) + (47702467081/16656250000000000000000000 : ℝ)*base65 + (286627923202703151/53300000000000000000000000000000 : ℝ)*base68 + (15871145672503151/53300000000000000000000000000000 : ℝ)*base70 + (408675414198696849/53300000000000000000000000000000 : ℝ)*base71 + (1292549683203/266500000000000000000000000 : ℝ)*base74 + (231828365172603151/53300000000000000000000000000000 : ℝ)*base76 + (340118638366996849/53300000000000000000000000000000 : ℝ)*base77 + (276557305488403151/53300000000000000000000000000000 : ℝ)*base80 + (416186406101/533000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1830287/156250000000000000000 : ℝ)*base90 + (1830287/156250000000000000000 : ℝ)*base92 + (1830287/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1138_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10623/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1481/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s4_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167989717/10000000000 : ℝ)*x 0 + (2701040709/5000000000 : ℝ)*x 1 + (105144629/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167989717/10000000000 : ℝ)^8331 ≤ (13171618233819/100000000000000 : ℝ)^6283 := by
    have hnat : (2167989717 : ℕ)^8331*100000000000000^6283 ≤ 13171618233819^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167989717 10000000000 13171618233819 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701040709/5000000000 : ℝ)^8331 ≤ (44196414113137/100000000000000 : ℝ)^6283 := by
    have hnat : (2701040709 : ℕ)^8331*100000000000000^6283 ≤ 44196414113137^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701040709 5000000000 44196414113137 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105144629/200000000 : ℝ)^8331 ≤ (42631967642411/100000000000000 : ℝ)^6283 := by
    have hnat : (105144629 : ℕ)^8331*100000000000000^6283 ≤ 42631967642411^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105144629 200000000 42631967642411 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167989717/10000000000 : ℝ), (2701040709/5000000000 : ℝ), (105144629/200000000 : ℝ)] ![(13171618233819/100000000000000 : ℝ), (44196414113137/100000000000000 : ℝ), (42631967642411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167989717/10000000000 : ℝ)|^8331 ≤ (13171618233819/100000000000000 : ℝ)^6283
        have hw : |(-2167989717/10000000000 : ℝ)|=(2167989717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701040709/5000000000 : ℝ)|^8331 ≤ (44196414113137/100000000000000 : ℝ)^6283
        have hw : |(2701040709/5000000000 : ℝ)|=(2701040709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105144629/200000000 : ℝ)|^8331 ≤ (42631967642411/100000000000000 : ℝ)^6283
        have hw : |(105144629/200000000 : ℝ)|=(105144629/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347022251/10000000000 : ℝ)*x 0 + (-280200609/1250000000 : ℝ)*x 1 + (105144639/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347022251/10000000000 : ℝ)^8331 ≤ (10900029512357/25000000000000 : ℝ)^6283 := by
    have hnat : (5347022251 : ℕ)^8331*25000000000000^6283 ≤ 10900029512357^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347022251 10000000000 10900029512357 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280200609/1250000000 : ℝ)^8331 ≤ (13767908914681/100000000000000 : ℝ)^6283 := by
    have hnat : (280200609 : ℕ)^8331*100000000000000^6283 ≤ 13767908914681^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280200609 1250000000 13767908914681 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105144639/200000000 : ℝ)^8331 ≤ (42631973018647/100000000000000 : ℝ)^6283 := by
    have hnat : (105144639 : ℕ)^8331*100000000000000^6283 ≤ 42631973018647^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105144639 200000000 42631973018647 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347022251/10000000000 : ℝ), (-280200609/1250000000 : ℝ), (105144639/200000000 : ℝ)] ![(10900029512357/25000000000000 : ℝ), (13767908914681/100000000000000 : ℝ), (42631973018647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347022251/10000000000 : ℝ)|^8331 ≤ (10900029512357/25000000000000 : ℝ)^6283
        have hw : |(5347022251/10000000000 : ℝ)|=(5347022251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280200609/1250000000 : ℝ)|^8331 ≤ (13767908914681/100000000000000 : ℝ)^6283
        have hw : |(-280200609/1250000000 : ℝ)|=(280200609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105144639/200000000 : ℝ)|^8331 ≤ (42631973018647/100000000000000 : ℝ)^6283
        have hw : |(105144639/200000000 : ℝ)|=(105144639/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673511421/5000000000 : ℝ)*x 0 + (1051446193/2000000000 : ℝ)*x 1 + (-2241605387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673511421/5000000000 : ℝ)^8331 ≤ (10900031109829/25000000000000 : ℝ)^6283 := by
    have hnat : (2673511421 : ℕ)^8331*25000000000000^6283 ≤ 10900031109829^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673511421 5000000000 10900031109829 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051446193/2000000000 : ℝ)^8331 ≤ (21315981213731/50000000000000 : ℝ)^6283 := by
    have hnat : (1051446193 : ℕ)^8331*50000000000000^6283 ≤ 21315981213731^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051446193 2000000000 21315981213731 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241605387/10000000000 : ℝ)^8331 ≤ (13767913108853/100000000000000 : ℝ)^6283 := by
    have hnat : (2241605387 : ℕ)^8331*100000000000000^6283 ≤ 13767913108853^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241605387 10000000000 13767913108853 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673511421/5000000000 : ℝ), (1051446193/2000000000 : ℝ), (-2241605387/10000000000 : ℝ)] ![(10900031109829/25000000000000 : ℝ), (21315981213731/50000000000000 : ℝ), (13767913108853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673511421/5000000000 : ℝ)|^8331 ≤ (10900031109829/25000000000000 : ℝ)^6283
        have hw : |(2673511421/5000000000 : ℝ)|=(2673511421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051446193/2000000000 : ℝ)|^8331 ≤ (21315981213731/50000000000000 : ℝ)^6283
        have hw : |(1051446193/2000000000 : ℝ)|=(1051446193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241605387/10000000000 : ℝ)|^8331 ≤ (13767913108853/100000000000000 : ℝ)^6283
        have hw : |(-2241605387/10000000000 : ℝ)|=(2241605387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364764741/10000000000 : ℝ)*x 0 + (1055788159/2500000000 : ℝ)*x 1 + (36088833/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364764741/10000000000 : ℝ)^8331 ≤ (33312164980107/100000000000000 : ℝ)^6283 := by
    have hnat : (4364764741 : ℕ)^8331*100000000000000^6283 ≤ 33312164980107^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364764741 10000000000 33312164980107 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055788159/2500000000 : ℝ)^8331 ≤ (31886712093903/100000000000000 : ℝ)^6283 := by
    have hnat : (1055788159 : ℕ)^8331*100000000000000^6283 ≤ 31886712093903^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055788159 2500000000 31886712093903 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36088833/80000000 : ℝ)^8331 ≤ (870028072947/2500000000000 : ℝ)^6283 := by
    have hnat : (36088833 : ℕ)^8331*2500000000000^6283 ≤ 870028072947^6283*80000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36088833 80000000 870028072947 2500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364764741/10000000000 : ℝ), (1055788159/2500000000 : ℝ), (36088833/80000000 : ℝ)] ![(33312164980107/100000000000000 : ℝ), (31886712093903/100000000000000 : ℝ), (870028072947/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364764741/10000000000 : ℝ)|^8331 ≤ (33312164980107/100000000000000 : ℝ)^6283
        have hw : |(4364764741/10000000000 : ℝ)|=(4364764741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055788159/2500000000 : ℝ)|^8331 ≤ (31886712093903/100000000000000 : ℝ)^6283
        have hw : |(1055788159/2500000000 : ℝ)|=(1055788159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36088833/80000000 : ℝ)|^8331 ≤ (870028072947/2500000000000 : ℝ)^6283
        have hw : |(36088833/80000000 : ℝ)|=(36088833/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167996889/10000000000 : ℝ)*x 0 + (5257644943/10000000000 : ℝ)*x 1 + (1350416559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167996889/10000000000 : ℝ)^8331 ≤ (13171676010489/100000000000000 : ℝ)^6283 := by
    have hnat : (2167996889 : ℕ)^8331*100000000000000^6283 ≤ 13171676010489^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167996889 10000000000 13171676010489 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257644943/10000000000 : ℝ)^8331 ≤ (42636413771663/100000000000000 : ℝ)^6283 := by
    have hnat : (5257644943 : ℕ)^8331*100000000000000^6283 ≤ 42636413771663^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257644943 10000000000 42636413771663 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350416559/2500000000 : ℝ)^8331 ≤ (4419191020981/10000000000000 : ℝ)^6283 := by
    have hnat : (1350416559 : ℕ)^8331*10000000000000^6283 ≤ 4419191020981^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350416559 2500000000 4419191020981 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167996889/10000000000 : ℝ), (5257644943/10000000000 : ℝ), (1350416559/2500000000 : ℝ)] ![(13171676010489/100000000000000 : ℝ), (42636413771663/100000000000000 : ℝ), (4419191020981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167996889/10000000000 : ℝ)|^8331 ≤ (13171676010489/100000000000000 : ℝ)^6283
        have hw : |(-2167996889/10000000000 : ℝ)|=(2167996889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257644943/10000000000 : ℝ)|^8331 ≤ (42636413771663/100000000000000 : ℝ)^6283
        have hw : |(5257644943/10000000000 : ℝ)|=(5257644943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350416559/2500000000 : ℝ)|^8331 ≤ (4419191020981/10000000000000 : ℝ)^6283
        have hw : |(1350416559/2500000000 : ℝ)|=(1350416559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655169059/5000000000 : ℝ)*x 0 + (-2097169727/10000000000 : ℝ)*x 1 + (2700832839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655169059/5000000000 : ℝ)^8331 ≤ (21601966820913/50000000000000 : ℝ)^6283 := by
    have hnat : (2655169059 : ℕ)^8331*50000000000000^6283 ≤ 21601966820913^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655169059 5000000000 21601966820913 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097169727/10000000000 : ℝ)^8331 ≤ (6302081093599/50000000000000 : ℝ)^6283 := by
    have hnat : (2097169727 : ℕ)^8331*50000000000000^6283 ≤ 6302081093599^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097169727 10000000000 6302081093599 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700832839/5000000000 : ℝ)^8331 ≤ (4419190415669/10000000000000 : ℝ)^6283 := by
    have hnat : (2700832839 : ℕ)^8331*10000000000000^6283 ≤ 4419190415669^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700832839 5000000000 4419190415669 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655169059/5000000000 : ℝ), (-2097169727/10000000000 : ℝ), (2700832839/5000000000 : ℝ)] ![(21601966820913/50000000000000 : ℝ), (6302081093599/50000000000000 : ℝ), (4419190415669/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655169059/5000000000 : ℝ)|^8331 ≤ (21601966820913/50000000000000 : ℝ)^6283
        have hw : |(2655169059/5000000000 : ℝ)|=(2655169059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097169727/10000000000 : ℝ)|^8331 ≤ (6302081093599/50000000000000 : ℝ)^6283
        have hw : |(-2097169727/10000000000 : ℝ)|=(2097169727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700832839/5000000000 : ℝ)|^8331 ≤ (4419190415669/10000000000000 : ℝ)^6283
        have hw : |(2700832839/5000000000 : ℝ)|=(2700832839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310337019/10000000000 : ℝ)*x 0 + (337604191/625000000 : ℝ)*x 1 + (-2097169339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310337019/10000000000 : ℝ)^8331 ≤ (43203921786081/100000000000000 : ℝ)^6283 := by
    have hnat : (5310337019 : ℕ)^8331*100000000000000^6283 ≤ 43203921786081^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310337019 10000000000 43203921786081 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337604191/625000000 : ℝ)^8331 ≤ (44191919105077/100000000000000 : ℝ)^6283 := by
    have hnat : (337604191 : ℕ)^8331*100000000000000^6283 ≤ 44191919105077^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337604191 625000000 44191919105077 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097169339/10000000000 : ℝ)^8331 ≤ (12604159095179/100000000000000 : ℝ)^6283 := by
    have hnat : (2097169339 : ℕ)^8331*100000000000000^6283 ≤ 12604159095179^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097169339 10000000000 12604159095179 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310337019/10000000000 : ℝ), (337604191/625000000 : ℝ), (-2097169339/10000000000 : ℝ)] ![(43203921786081/100000000000000 : ℝ), (44191919105077/100000000000000 : ℝ), (12604159095179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310337019/10000000000 : ℝ)|^8331 ≤ (43203921786081/100000000000000 : ℝ)^6283
        have hw : |(5310337019/10000000000 : ℝ)|=(5310337019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337604191/625000000 : ℝ)|^8331 ≤ (44191919105077/100000000000000 : ℝ)^6283
        have hw : |(337604191/625000000 : ℝ)|=(337604191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097169339/10000000000 : ℝ)|^8331 ≤ (12604159095179/100000000000000 : ℝ)^6283
        have hw : |(-2097169339/10000000000 : ℝ)|=(2097169339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s4_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545597269/1250000000 : ℝ)*x 0 + (2255141599/5000000000 : ℝ)*x 1 + (1055994449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545597269/1250000000 : ℝ)^8331 ≤ (33312300696863/100000000000000 : ℝ)^6283 := by
    have hnat : (545597269 : ℕ)^8331*100000000000000^6283 ≤ 33312300696863^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545597269 1250000000 33312300696863 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255141599/5000000000 : ℝ)^8331 ≤ (8698181440869/25000000000000 : ℝ)^6283 := by
    have hnat : (2255141599 : ℕ)^8331*25000000000000^6283 ≤ 8698181440869^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255141599 5000000000 8698181440869 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055994449/2500000000 : ℝ)^8331 ≤ (31894973520211/100000000000000 : ℝ)^6283 := by
    have hnat : (1055994449 : ℕ)^8331*100000000000000^6283 ≤ 31894973520211^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055994449 2500000000 31894973520211 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545597269/1250000000 : ℝ), (2255141599/5000000000 : ℝ), (1055994449/2500000000 : ℝ)] ![(33312300696863/100000000000000 : ℝ), (8698181440869/25000000000000 : ℝ), (31894973520211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545597269/1250000000 : ℝ)|^8331 ≤ (33312300696863/100000000000000 : ℝ)^6283
        have hw : |(545597269/1250000000 : ℝ)|=(545597269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255141599/5000000000 : ℝ)|^8331 ≤ (8698181440869/25000000000000 : ℝ)^6283
        have hw : |(2255141599/5000000000 : ℝ)|=(2255141599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055994449/2500000000 : ℝ)|^8331 ≤ (31894973520211/100000000000000 : ℝ)^6283
        have hw : |(1055994449/2500000000 : ℝ)|=(1055994449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1481/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (349/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1481/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10623/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1481/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10623/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1481/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10623/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1481/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10623/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1481/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10623/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1481/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10623/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (10623/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (1368625209726547/12500000000000000000 : ℝ) := by
    have hpowers : (10623/100000 : ℝ)^4165 ≤ (1368625209726547/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10623 : ℕ)^4165*12500000000000000000^1024 ≤ 1368625209726547^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10623 100000 1368625209726547 12500000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10623/100000 : ℝ)) (X := (1368625209726547/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1481/10000 : ℝ) ^ (4165/1024 : ℝ) ≤ (42298980605276209/100000000000000000000 : ℝ) := by
    have hpowers : (1481/10000 : ℝ)^4165 ≤ (42298980605276209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1481 : ℕ)^4165*100000000000000000000^1024 ≤ 42298980605276209^1024*10000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1481 10000 42298980605276209 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1481/10000 : ℝ)) (X := (42298980605276209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251368625209726547/6250000000000000000 : ℝ) ≤ (10000538336233811/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (6251368625209726547/6250000000000000000 : ℝ)^1024 ≤ (10000538336233811/10000000000000000 : ℝ)^4165 := by
      have hnat : (6251368625209726547 : ℕ)^1024*10000000000000000^4165 ≤ 10000538336233811^4165*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251368625209726547 6250000000000000000 10000538336233811 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538336233811/10000000000000000 : ℝ)) (X := (6251368625209726547/6250000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010649596456617717/20000000000000000000 : ℝ) ≤ (2000261776659813/2000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (20010649596456617717/20000000000000000000 : ℝ)^1024 ≤ (2000261776659813/2000000000000000 : ℝ)^4165 := by
      have hnat : (20010649596456617717 : ℕ)^1024*2000000000000000^4165 ≤ 2000261776659813^4165*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010649596456617717 20000000000000000000 2000261776659813 2000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000261776659813/2000000000000000 : ℝ)) (X := (20010649596456617717/20000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042298980605276209/50000000000000000000 : ℝ) ≤ (10002079430364319/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50042298980605276209/50000000000000000000 : ℝ)^1024 ≤ (10002079430364319/10000000000000000 : ℝ)^4165 := by
      have hnat : (50042298980605276209 : ℕ)^1024*10000000000000000^4165 ≤ 10002079430364319^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042298980605276209 50000000000000000000 10002079430364319 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002079430364319/10000000000000000 : ℝ)) (X := (50042298980605276209/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1368625209726547/12500000000000000000 : ℝ) ≤ ((41855882970862580173/41870000000000000000 : ℝ)+2*(385273532627/209350000000000 : ℝ)*(10623/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (41855882970862580173/41870000000000000000 : ℝ)+2*(385273532627/209350000000000 : ℝ)*(10623/100000 : ℝ)=(10000538336233811/10000000000000000 : ℝ) by norm_num, show 1+2*(1368625209726547/12500000000000000000 : ℝ)=(6251368625209726547/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42298980605276209/100000000000000000000 : ℝ)+(1368625209726547/12500000000000000000 : ℝ) ≤ ((41855882970862580173/41870000000000000000 : ℝ)+(385273532627/209350000000000 : ℝ)*((1481/10000 : ℝ)+(10623/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (41855882970862580173/41870000000000000000 : ℝ)+(385273532627/209350000000000 : ℝ)*((1481/10000 : ℝ)+(10623/100000 : ℝ))=(2000261776659813/2000000000000000 : ℝ) by norm_num, show 1+(42298980605276209/100000000000000000000 : ℝ)+(1368625209726547/12500000000000000000 : ℝ)=(20010649596456617717/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42298980605276209/100000000000000000000 : ℝ) ≤ ((41855882970862580173/41870000000000000000 : ℝ)+2*(385273532627/209350000000000 : ℝ)*(1481/10000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (41855882970862580173/41870000000000000000 : ℝ)+2*(385273532627/209350000000000 : ℝ)*(1481/10000 : ℝ)=(10002079430364319/10000000000000000 : ℝ) by norm_num, show 1+2*(42298980605276209/100000000000000000000 : ℝ)=(50042298980605276209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41855882970862580173/41870000000000000000 : ℝ)*(X 1 0+X 2 0)+(385273532627/209350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (10623/100000 : ℝ)) (hi := (1481/10000 : ℝ)) (c := (41855882970862580173/41870000000000000000 : ℝ)) (alpha := (385273532627/209350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41855882970862580173/41870000000000000000 : ℝ)*(X 0 1+X 2 1)+(385273532627/209350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (10623/100000 : ℝ)) (hi := (1481/10000 : ℝ)) (c := (41855882970862580173/41870000000000000000 : ℝ)) (alpha := (385273532627/209350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41855882970862580173/41870000000000000000 : ℝ)*(X 0 2+X 1 2)+(385273532627/209350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (10623/100000 : ℝ)) (hi := (1481/10000 : ℝ)) (c := (41855882970862580173/41870000000000000000 : ℝ)) (alpha := (385273532627/209350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2167989717/10000000000 : ℝ)*X 0 0+(2701040709/5000000000 : ℝ)*X 0 1+(105144629/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347022251/10000000000 : ℝ)*X 1 0+(-280200609/1250000000 : ℝ)*X 1 1+(105144639/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673511421/5000000000 : ℝ)*X 2 0+(1051446193/2000000000 : ℝ)*X 2 1+(-2241605387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364764741/10000000000 : ℝ)*X 0 0+(1055788159/2500000000 : ℝ)*X 0 1+(36088833/80000000 : ℝ)*X 0 2+(4364764741/10000000000 : ℝ)*X 1 0+(1055788159/2500000000 : ℝ)*X 1 1+(36088833/80000000 : ℝ)*X 1 2+(4364764741/10000000000 : ℝ)*X 2 0+(1055788159/2500000000 : ℝ)*X 2 1+(36088833/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167996889/10000000000 : ℝ)*X 0 0+(5257644943/10000000000 : ℝ)*X 0 1+(1350416559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655169059/5000000000 : ℝ)*X 1 0+(-2097169727/10000000000 : ℝ)*X 1 1+(2700832839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310337019/10000000000 : ℝ)*X 2 0+(337604191/625000000 : ℝ)*X 2 1+(-2097169339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545597269/1250000000 : ℝ)*X 0 0+(2255141599/5000000000 : ℝ)*X 0 1+(1055994449/2500000000 : ℝ)*X 0 2+(545597269/1250000000 : ℝ)*X 1 0+(2255141599/5000000000 : ℝ)*X 1 1+(1055994449/2500000000 : ℝ)*X 1 2+(545597269/1250000000 : ℝ)*X 2 0+(2255141599/5000000000 : ℝ)*X 2 1+(1055994449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12536133912589765464791776857/2093500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9110367/20000000000000 : ℝ)*(base15) + (14431837/3125000000000 : ℝ)*(base29) + (203572239/50000000000000 : ℝ)*(lower2) + (19824437/25000000000000 : ℝ)*(upper3) + (137887511/100000000000000 : ℝ)*(lower4) + (5188258736649919/100000000000000 : ℝ)*(major0) + (5188259198468703/100000000000000 : ℝ)*(major1) + (5188259198468703/100000000000000 : ℝ)*(major2) + (6903687135230217/100000000000000 : ℝ)*(sp0) + (3451843313929799/50000000000000 : ℝ)*(sp1) + (215739207171859/3125000000000 : ℝ)*(sp2) + (173640800903147/5000000000000 : ℝ)*(sp3) + (6408782389/20000000000000 : ℝ)*(sp6) + (15044040141/100000000000000 : ℝ)*(sp7) + (3472831062103081/100000000000000 : ℝ)*(f.failure) + (6903687135230217/100000000000000 : ℝ)*(f.sum) + (187473780462457/20935000000000000000000000000 : ℝ)*base65 + (1892822299042974381/4187000000000000000000000000000000 : ℝ)*base68 + (105569074536543025619/4187000000000000000000000000000000 : ℝ)*base69 + (588568145229037655987/4187000000000000000000000000000000 : ℝ)*base71 + (6022617930789/1308437500000000000000000000 : ℝ)*base73 + (138985573237720574381/4187000000000000000000000000000000 : ℝ)*base76 + (238210196770773344013/4187000000000000000000000000000000 : ℝ)*base78 + (4069537667214574381/4187000000000000000000000000000000 : ℝ)*base80 + (1228527917389119/20935000000000000000000000000 : ℝ)*base81 + (32956189/10000000000000000000000 : ℝ)*base89 + (32956189/10000000000000000000000 : ℝ)*base91 + (32956189/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1933821202033624976797040727/261687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94138261/50000000000000 : ℝ)*(base19) + (7214989/5000000000000 : ℝ)*(upper2) + (170992899/100000000000000 : ℝ)*(lower3) + (203347471/50000000000000 : ℝ)*(lower4) + (652264709096933/12500000000000 : ℝ)*(major0) + (652264709096933/12500000000000 : ℝ)*(major1) + (652264709096933/12500000000000 : ℝ)*(major2) + (2247969131/25000000000000 : ℝ)*(sp0) + (15279158623/50000000000000 : ℝ)*(sp2) + (3540787399/12500000000000 : ℝ)*(sp3) + (6943408873953891/100000000000000 : ℝ)*(sp4) + (6943417677553893/100000000000000 : ℝ)*(sp5) + (6943387307513169/100000000000000 : ℝ)*(sp6) + (3492788907094277/100000000000000 : ℝ)*(sp7) + (3492817233393469/100000000000000 : ℝ)*(f.failure) + (1388683573166083/20000000000000 : ℝ)*(f.sum) + (126687880155841/20935000000000000000000000000 : ℝ)*base65 + (1955741671756015591/523375000000000000000000000000000 : ℝ)*base68 + (9109891862037890591/523375000000000000000000000000000 : ℝ)*base70 + (1340795174542140591/523375000000000000000000000000000 : ℝ)*base72 + (29657207939411/20935000000000000000000000000 : ℝ)*base73 + (3718877057626359409/523375000000000000000000000000000 : ℝ)*base75 + (1475986586557484409/523375000000000000000000000000000 : ℝ)*base77 + (5910378144991390591/523375000000000000000000000000000 : ℝ)*base80 + (90174318636209/20935000000000000000000000000 : ℝ)*base82 + (41485761/10000000000000000000000 : ℝ)*base89 + (41485761/10000000000000000000000 : ℝ)*base91 + (41485761/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1138_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1481/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s5_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271079351/1250000000 : ℝ)*x 0 + (215800641/400000000 : ℝ)*x 1 + (5263873497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271079351/1250000000 : ℝ)^8331 ≤ (527072609983/4000000000000 : ℝ)^6283 := by
    have hnat : (271079351 : ℕ)^8331*4000000000000^6283 ≤ 527072609983^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271079351 1250000000 527072609983 4000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215800641/400000000 : ℝ)^8331 ≤ (1378743248739/3125000000000 : ℝ)^6283 := by
    have hnat : (215800641 : ℕ)^8331*3125000000000^6283 ≤ 1378743248739^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215800641 400000000 1378743248739 3125000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263873497/10000000000 : ℝ)^8331 ≤ (21351700387063/50000000000000 : ℝ)^6283 := by
    have hnat : (5263873497 : ℕ)^8331*50000000000000^6283 ≤ 21351700387063^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263873497 10000000000 21351700387063 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271079351/1250000000 : ℝ), (215800641/400000000 : ℝ), (5263873497/10000000000 : ℝ)] ![(527072609983/4000000000000 : ℝ), (1378743248739/3125000000000 : ℝ), (21351700387063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271079351/1250000000 : ℝ)|^8331 ≤ (527072609983/4000000000000 : ℝ)^6283
        have hw : |(-271079351/1250000000 : ℝ)|=(271079351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215800641/400000000 : ℝ)|^8331 ≤ (1378743248739/3125000000000 : ℝ)^6283
        have hw : |(215800641/400000000 : ℝ)|=(215800641/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263873497/10000000000 : ℝ)|^8331 ≤ (21351700387063/50000000000000 : ℝ)^6283
        have hw : |(5263873497/10000000000 : ℝ)|=(5263873497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345252249/10000000000 : ℝ)*x 0 + (-44703619/200000000 : ℝ)*x 1 + (5263873551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345252249/10000000000 : ℝ)^8331 ≤ (1361905682283/3125000000000 : ℝ)^6283 := by
    have hnat : (5345252249 : ℕ)^8331*3125000000000^6283 ≤ 1361905682283^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345252249 10000000000 1361905682283 3125000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44703619/200000000 : ℝ)^8331 ≤ (13715616796307/100000000000000 : ℝ)^6283 := by
    have hnat : (44703619 : ℕ)^8331*100000000000000^6283 ≤ 13715616796307^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44703619 200000000 13715616796307 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263873551/10000000000 : ℝ)^8331 ≤ (42703401354999/100000000000000 : ℝ)^6283 := by
    have hnat : (5263873551 : ℕ)^8331*100000000000000^6283 ≤ 42703401354999^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263873551 10000000000 42703401354999 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345252249/10000000000 : ℝ), (-44703619/200000000 : ℝ), (5263873551/10000000000 : ℝ)] ![(1361905682283/3125000000000 : ℝ), (13715616796307/100000000000000 : ℝ), (42703401354999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345252249/10000000000 : ℝ)|^8331 ≤ (1361905682283/3125000000000 : ℝ)^6283
        have hw : |(5345252249/10000000000 : ℝ)|=(5345252249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44703619/200000000 : ℝ)|^8331 ≤ (13715616796307/100000000000000 : ℝ)^6283
        have hw : |(-44703619/200000000 : ℝ)|=(44703619/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263873551/10000000000 : ℝ)|^8331 ≤ (42703401354999/100000000000000 : ℝ)^6283
        have hw : |(5263873551/10000000000 : ℝ)|=(5263873551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069050411/2000000000 : ℝ)*x 0 + (2631936869/5000000000 : ℝ)*x 1 + (-2235180961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069050411/2000000000 : ℝ)^8331 ≤ (10895244933939/25000000000000 : ℝ)^6283 := by
    have hnat : (1069050411 : ℕ)^8331*25000000000000^6283 ≤ 10895244933939^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069050411 2000000000 10895244933939 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631936869/5000000000 : ℝ)^8331 ≤ (42703403366539/100000000000000 : ℝ)^6283 := by
    have hnat : (2631936869 : ℕ)^8331*100000000000000^6283 ≤ 42703403366539^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631936869 5000000000 42703403366539 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235180961/10000000000 : ℝ)^8331 ≤ (13715616885807/100000000000000 : ℝ)^6283 := by
    have hnat : (2235180961 : ℕ)^8331*100000000000000^6283 ≤ 13715616885807^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235180961 10000000000 13715616885807 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069050411/2000000000 : ℝ), (2631936869/5000000000 : ℝ), (-2235180961/10000000000 : ℝ)] ![(10895244933939/25000000000000 : ℝ), (42703403366539/100000000000000 : ℝ), (13715616885807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069050411/2000000000 : ℝ)|^8331 ≤ (10895244933939/25000000000000 : ℝ)^6283
        have hw : |(1069050411/2000000000 : ℝ)|=(1069050411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631936869/5000000000 : ℝ)|^8331 ≤ (42703403366539/100000000000000 : ℝ)^6283
        have hw : |(2631936869/5000000000 : ℝ)|=(2631936869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235180961/10000000000 : ℝ)|^8331 ≤ (13715616885807/100000000000000 : ℝ)^6283
        have hw : |(-2235180961/10000000000 : ℝ)|=(2235180961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091285323/2500000000 : ℝ)*x 0 + (132397809/312500000 : ℝ)*x 1 + (2248714711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091285323/2500000000 : ℝ)^8331 ≤ (33315975655929/100000000000000 : ℝ)^6283 := by
    have hnat : (1091285323 : ℕ)^8331*100000000000000^6283 ≤ 33315975655929^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091285323 2500000000 33315975655929 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132397809/312500000 : ℝ)^8331 ≤ (32022713140419/100000000000000 : ℝ)^6283 := by
    have hnat : (132397809 : ℕ)^8331*100000000000000^6283 ≤ 32022713140419^6283*312500000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132397809 312500000 32022713140419 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248714711/5000000000 : ℝ)^8331 ≤ (17330655591919/50000000000000 : ℝ)^6283 := by
    have hnat : (2248714711 : ℕ)^8331*50000000000000^6283 ≤ 17330655591919^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248714711 5000000000 17330655591919 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091285323/2500000000 : ℝ), (132397809/312500000 : ℝ), (2248714711/5000000000 : ℝ)] ![(33315975655929/100000000000000 : ℝ), (32022713140419/100000000000000 : ℝ), (17330655591919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091285323/2500000000 : ℝ)|^8331 ≤ (33315975655929/100000000000000 : ℝ)^6283
        have hw : |(1091285323/2500000000 : ℝ)|=(1091285323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132397809/312500000 : ℝ)|^8331 ≤ (32022713140419/100000000000000 : ℝ)^6283
        have hw : |(132397809/312500000 : ℝ)|=(132397809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248714711/5000000000 : ℝ)|^8331 ≤ (17330655591919/50000000000000 : ℝ)^6283
        have hw : |(2248714711/5000000000 : ℝ)|=(2248714711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542160009/2500000000 : ℝ)*x 0 + (1316053153/2500000000 : ℝ)*x 1 + (337167233/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542160009/2500000000 : ℝ)^8331 ≤ (329421434243/2500000000000 : ℝ)^6283 := by
    have hnat : (542160009 : ℕ)^8331*2500000000000^6283 ≤ 329421434243^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542160009 2500000000 329421434243 2500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316053153/2500000000 : ℝ)^8331 ≤ (10676762159563/25000000000000 : ℝ)^6283 := by
    have hnat : (1316053153 : ℕ)^8331*25000000000000^6283 ≤ 10676762159563^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316053153 2500000000 10676762159563 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337167233/625000000 : ℝ)^8331 ≤ (2205804698831/5000000000000 : ℝ)^6283 := by
    have hnat : (337167233 : ℕ)^8331*5000000000000^6283 ≤ 2205804698831^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337167233 625000000 2205804698831 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542160009/2500000000 : ℝ), (1316053153/2500000000 : ℝ), (337167233/625000000 : ℝ)] ![(329421434243/2500000000000 : ℝ), (10676762159563/25000000000000 : ℝ), (2205804698831/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542160009/2500000000 : ℝ)|^8331 ≤ (329421434243/2500000000000 : ℝ)^6283
        have hw : |(-542160009/2500000000 : ℝ)|=(542160009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316053153/2500000000 : ℝ)|^8331 ≤ (10676762159563/25000000000000 : ℝ)^6283
        have hw : |(1316053153/2500000000 : ℝ)|=(1316053153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337167233/625000000 : ℝ)|^8331 ≤ (2205804698831/5000000000000 : ℝ)^6283
        have hw : |(337167233/625000000 : ℝ)|=(337167233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312036981/10000000000 : ℝ)*x 0 + (-2104378839/10000000000 : ℝ)*x 1 + (2697337857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312036981/10000000000 : ℝ)^8331 ≤ (43222261520047/100000000000000 : ℝ)^6283 := by
    have hnat : (5312036981 : ℕ)^8331*100000000000000^6283 ≤ 43222261520047^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312036981 10000000000 43222261520047 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104378839/10000000000 : ℝ)^8331 ≤ (3165411160543/25000000000000 : ℝ)^6283 := by
    have hnat : (2104378839 : ℕ)^8331*25000000000000^6283 ≤ 3165411160543^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104378839 10000000000 3165411160543 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697337857/5000000000 : ℝ)^8331 ≤ (22058046912407/50000000000000 : ℝ)^6283 := by
    have hnat : (2697337857 : ℕ)^8331*50000000000000^6283 ≤ 22058046912407^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697337857 5000000000 22058046912407 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312036981/10000000000 : ℝ), (-2104378839/10000000000 : ℝ), (2697337857/5000000000 : ℝ)] ![(43222261520047/100000000000000 : ℝ), (3165411160543/25000000000000 : ℝ), (22058046912407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312036981/10000000000 : ℝ)|^8331 ≤ (43222261520047/100000000000000 : ℝ)^6283
        have hw : |(5312036981/10000000000 : ℝ)|=(5312036981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104378839/10000000000 : ℝ)|^8331 ≤ (3165411160543/25000000000000 : ℝ)^6283
        have hw : |(-2104378839/10000000000 : ℝ)|=(2104378839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697337857/5000000000 : ℝ)|^8331 ≤ (22058046912407/50000000000000 : ℝ)^6283
        have hw : |(2697337857/5000000000 : ℝ)|=(2697337857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212481479/400000000 : ℝ)*x 0 + (2697337859/5000000000 : ℝ)*x 1 + (-1052189421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212481479/400000000 : ℝ)^8331 ≤ (21611130727657/50000000000000 : ℝ)^6283 := by
    have hnat : (212481479 : ℕ)^8331*50000000000000^6283 ≤ 21611130727657^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212481479 400000000 21611130727657 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697337859/5000000000 : ℝ)^8331 ≤ (44116093868187/100000000000000 : ℝ)^6283 := by
    have hnat : (2697337859 : ℕ)^8331*100000000000000^6283 ≤ 44116093868187^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697337859 5000000000 44116093868187 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052189421/5000000000 : ℝ)^8331 ≤ (6330822333053/50000000000000 : ℝ)^6283 := by
    have hnat : (1052189421 : ℕ)^8331*50000000000000^6283 ≤ 6330822333053^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052189421 5000000000 6330822333053 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212481479/400000000 : ℝ), (2697337859/5000000000 : ℝ), (-1052189421/5000000000 : ℝ)] ![(21611130727657/50000000000000 : ℝ), (44116093868187/100000000000000 : ℝ), (6330822333053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212481479/400000000 : ℝ)|^8331 ≤ (21611130727657/50000000000000 : ℝ)^6283
        have hw : |(212481479/400000000 : ℝ)|=(212481479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697337859/5000000000 : ℝ)|^8331 ≤ (44116093868187/100000000000000 : ℝ)^6283
        have hw : |(2697337859/5000000000 : ℝ)|=(2697337859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052189421/5000000000 : ℝ)|^8331 ≤ (6330822333053/50000000000000 : ℝ)^6283
        have hw : |(-1052189421/5000000000 : ℝ)|=(1052189421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s5_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272821993/625000000 : ℝ)*x 0 + (4496755601/10000000000 : ℝ)*x 1 + (211870311/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272821993/625000000 : ℝ)^8331 ≤ (8329020722107/25000000000000 : ℝ)^6283 := by
    have hnat : (272821993 : ℕ)^8331*25000000000000^6283 ≤ 8329020722107^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272821993 625000000 8329020722107 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496755601/10000000000 : ℝ)^8331 ≤ (34654425538617/100000000000000 : ℝ)^6283 := by
    have hnat : (4496755601 : ℕ)^8331*100000000000000^6283 ≤ 34654425538617^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496755601 10000000000 34654425538617 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211870311/500000000 : ℝ)^8331 ≤ (32029491563277/100000000000000 : ℝ)^6283 := by
    have hnat : (211870311 : ℕ)^8331*100000000000000^6283 ≤ 32029491563277^6283*500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211870311 500000000 32029491563277 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272821993/625000000 : ℝ), (4496755601/10000000000 : ℝ), (211870311/500000000 : ℝ)] ![(8329020722107/25000000000000 : ℝ), (34654425538617/100000000000000 : ℝ), (32029491563277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272821993/625000000 : ℝ)|^8331 ≤ (8329020722107/25000000000000 : ℝ)^6283
        have hw : |(272821993/625000000 : ℝ)|=(272821993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496755601/10000000000 : ℝ)|^8331 ≤ (34654425538617/100000000000000 : ℝ)^6283
        have hw : |(4496755601/10000000000 : ℝ)|=(4496755601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211870311/500000000 : ℝ)|^8331 ≤ (32029491563277/100000000000000 : ℝ)^6283
        have hw : |(211870311/500000000 : ℝ)|=(211870311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (349/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (349/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (349/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (349/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (349/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (349/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (349/3125 : ℝ) ^ (4165/1024 : ℝ) ≤ (13419969424476947/100000000000000000000 : ℝ) := by
    have hpowers : (349/3125 : ℝ)^4165 ≤ (13419969424476947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (349 : ℕ)^4165*100000000000000000000^1024 ≤ 13419969424476947^1024*3125^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        349 3125 13419969424476947 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (349/3125 : ℝ)) (X := (13419969424476947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4165/1024 : ℝ) ≤ (36006485342508281/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4165 ≤ (36006485342508281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4165*100000000000000000000^1024 ≤ 36006485342508281^1024*20000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 36006485342508281 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (36006485342508281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013419969424476947/50000000000000000000 : ℝ) ≤ (5000329907758389/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50013419969424476947/50000000000000000000 : ℝ)^1024 ≤ (5000329907758389/5000000000000000 : ℝ)^4165 := by
      have hnat : (50013419969424476947 : ℕ)^1024*5000000000000000^4165 ≤ 5000329907758389^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013419969424476947 50000000000000000000 5000329907758389 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329907758389/5000000000000000 : ℝ)) (X := (50013419969424476947/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012356613691746307/25000000000000000000 : ℝ) ≤ (5000607482107813/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (25012356613691746307/25000000000000000000 : ℝ)^1024 ≤ (5000607482107813/5000000000000000 : ℝ)^4165 := by
      have hnat : (25012356613691746307 : ℕ)^1024*5000000000000000^4165 ≤ 5000607482107813^4165*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012356613691746307 25000000000000000000 5000607482107813 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000607482107813/5000000000000000 : ℝ)) (X := (25012356613691746307/25000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036006485342508281/50000000000000000000 : ℝ) ≤ (5000885056457237/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50036006485342508281/50000000000000000000 : ℝ)^1024 ≤ (5000885056457237/5000000000000000 : ℝ)^4165 := by
      have hnat : (50036006485342508281 : ℕ)^1024*5000000000000000^4165 ≤ 5000885056457237^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036006485342508281 50000000000000000000 5000885056457237 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000885056457237/5000000000000000 : ℝ)) (X := (50036006485342508281/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13419969424476947/100000000000000000000 : ℝ) ≤ ((15329811926426244599/15335000000000000000 : ℝ)+2*(17348396839/9584375000000 : ℝ)*(349/3125 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (15329811926426244599/15335000000000000000 : ℝ)+2*(17348396839/9584375000000 : ℝ)*(349/3125 : ℝ)=(5000329907758389/5000000000000000 : ℝ) by norm_num, show 1+2*(13419969424476947/100000000000000000000 : ℝ)=(50013419969424476947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36006485342508281/100000000000000000000 : ℝ)+(13419969424476947/100000000000000000000 : ℝ) ≤ ((15329811926426244599/15335000000000000000 : ℝ)+(17348396839/9584375000000 : ℝ)*((2847/20000 : ℝ)+(349/3125 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (15329811926426244599/15335000000000000000 : ℝ)+(17348396839/9584375000000 : ℝ)*((2847/20000 : ℝ)+(349/3125 : ℝ))=(5000607482107813/5000000000000000 : ℝ) by norm_num, show 1+(36006485342508281/100000000000000000000 : ℝ)+(13419969424476947/100000000000000000000 : ℝ)=(25012356613691746307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36006485342508281/100000000000000000000 : ℝ) ≤ ((15329811926426244599/15335000000000000000 : ℝ)+2*(17348396839/9584375000000 : ℝ)*(2847/20000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (15329811926426244599/15335000000000000000 : ℝ)+2*(17348396839/9584375000000 : ℝ)*(2847/20000 : ℝ)=(5000885056457237/5000000000000000 : ℝ) by norm_num, show 1+2*(36006485342508281/100000000000000000000 : ℝ)=(50036006485342508281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15329811926426244599/15335000000000000000 : ℝ)*(X 1 0+X 2 0)+(17348396839/9584375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15329811926426244599/15335000000000000000 : ℝ)) (alpha := (17348396839/9584375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15329811926426244599/15335000000000000000 : ℝ)*(X 0 1+X 2 1)+(17348396839/9584375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15329811926426244599/15335000000000000000 : ℝ)) (alpha := (17348396839/9584375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15329811926426244599/15335000000000000000 : ℝ)*(X 0 2+X 1 2)+(17348396839/9584375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15329811926426244599/15335000000000000000 : ℝ)) (alpha := (17348396839/9584375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271079351/1250000000 : ℝ)*X 0 0+(215800641/400000000 : ℝ)*X 0 1+(5263873497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345252249/10000000000 : ℝ)*X 1 0+(-44703619/200000000 : ℝ)*X 1 1+(5263873551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069050411/2000000000 : ℝ)*X 2 0+(2631936869/5000000000 : ℝ)*X 2 1+(-2235180961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091285323/2500000000 : ℝ)*X 0 0+(132397809/312500000 : ℝ)*X 0 1+(2248714711/5000000000 : ℝ)*X 0 2+(1091285323/2500000000 : ℝ)*X 1 0+(132397809/312500000 : ℝ)*X 1 1+(2248714711/5000000000 : ℝ)*X 1 2+(1091285323/2500000000 : ℝ)*X 2 0+(132397809/312500000 : ℝ)*X 2 1+(2248714711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542160009/2500000000 : ℝ)*X 0 0+(1316053153/2500000000 : ℝ)*X 0 1+(337167233/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312036981/10000000000 : ℝ)*X 1 0+(-2104378839/10000000000 : ℝ)*X 1 1+(2697337857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212481479/400000000 : ℝ)*X 2 0+(2697337859/5000000000 : ℝ)*X 2 1+(-1052189421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272821993/625000000 : ℝ)*X 0 0+(4496755601/10000000000 : ℝ)*X 0 1+(211870311/500000000 : ℝ)*X 0 2+(272821993/625000000 : ℝ)*X 1 0+(4496755601/10000000000 : ℝ)*X 1 1+(211870311/500000000 : ℝ)*X 1 2+(272821993/625000000 : ℝ)*X 2 0+(4496755601/10000000000 : ℝ)*X 2 1+(211870311/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (371559990814487243817289101/38337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1065784897/50000000000000 : ℝ)*(base19) + (367715441/20000000000000 : ℝ)*(base23) + (69051471/25000000000000 : ℝ)*(upper3) + (1735779/20000000000000 : ℝ)*(upper4) + (97986689/50000000000000 : ℝ)*(upper5) + (573065297509567/10000000000000 : ℝ)*(major0) + (573065297509567/10000000000000 : ℝ)*(major1) + (573065297509567/10000000000000 : ℝ)*(major2) + (3812678392342321/50000000000000 : ℝ)*(sp0) + (190635346634749/2500000000000 : ℝ)*(sp1) + (7625414158382549/100000000000000 : ℝ)*(sp2) + (3835861358570717/100000000000000 : ℝ)*(sp3) + (7401534389/12500000000000 : ℝ)*(sp4) + (1766975021/6250000000000 : ℝ)*(sp7) + (3835889630171053/100000000000000 : ℝ)*(f.failure) + (3812707998479877/50000000000000 : ℝ)*(f.sum) + (2561578564489/766750000000000000000000000 : ℝ)*base66 + (353513701168278633/153350000000000000000000000000000 : ℝ)*base67 + (1581606767076978633/153350000000000000000000000000000 : ℝ)*base69 + (139724088639178633/153350000000000000000000000000000 : ℝ)*base71 + (4405912827/11980468750000000000000000 : ℝ)*base74 + (849501902145521367/153350000000000000000000000000000 : ℝ)*base76 + (359571532069928633/153350000000000000000000000000000 : ℝ)*base77 + (1231734189115478633/153350000000000000000000000000000 : ℝ)*base79 + (9174856156997/3067000000000000000000000000 : ℝ)*base81 + (47369457/10000000000000000000000 : ℝ)*base89 + (47369457/10000000000000000000000 : ℝ)*base91 + (47369457/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128363517231075307015631577/23960937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1047466901/100000000000000 : ℝ)*(base19) + (1121376721/100000000000000 : ℝ)*(base23) + (107405363/100000000000000 : ℝ)*(upper3) + (37925061/100000000000000 : ℝ)*(lower4) + (1666793/1562500000000 : ℝ)*(upper5) + (360025090467241/6250000000000 : ℝ)*(major0) + (360025090467241/6250000000000 : ℝ)*(major1) + (360025090467241/6250000000000 : ℝ)*(major2) + (5569573223/20000000000000 : ℝ)*(sp1) + (926090483/3125000000000 : ℝ)*(sp2) + (306600021847429/4000000000000 : ℝ)*(sp4) + (7664971650852709/100000000000000 : ℝ)*(sp5) + (1916242447478387/25000000000000 : ℝ)*(sp6) + (963950542548167/25000000000000 : ℝ)*(sp7) + (963950542548167/25000000000000 : ℝ)*(f.failure) + (306600021847429/4000000000000 : ℝ)*(f.sum) + (17659485735187/3833750000000000000000000000 : ℝ)*base65 + (46707600960581359/95843750000000000000000000000000 : ℝ)*base67 + (852784132653918641/95843750000000000000000000000000 : ℝ)*base70 + (11146962478793641/95843750000000000000000000000000 : ℝ)*base72 + (103808647720943/15335000000000000000000000000 : ℝ)*base73 + (616380806903824891/95843750000000000000000000000000 : ℝ)*base76 + (344388513649793641/95843750000000000000000000000000 : ℝ)*base78 + (517754416588293641/95843750000000000000000000000000 : ℝ)*base80 + (11959311116751/1916875000000000000000000000 : ℝ)*base81 + (26311277/2500000000000000000000 : ℝ)*base90 + (26311277/2500000000000000000000 : ℝ)*base92 + (26311277/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1138_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1138_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1138_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1138_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1138_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8257/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
