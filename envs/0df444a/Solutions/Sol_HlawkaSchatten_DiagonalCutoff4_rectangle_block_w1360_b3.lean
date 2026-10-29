-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:39.021807+00:00
-- url     : https://prove2.me/submissions/daea2c1a-2171-438c-a505-48ac0f8834e0

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
theorem support_rectangle_w1360_s9_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014264149/5000000000 : ℝ)*x 0 + (541172603/1000000000 : ℝ)*x 1 + (5245192567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014264149/5000000000 : ℝ)^135 ≤ (12357663197333/100000000000000 : ℝ)^103 := by
    have hnat : (1014264149 : ℕ)^135*100000000000000^103 ≤ 12357663197333^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014264149 5000000000 12357663197333 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541172603/1000000000 : ℝ)^135 ≤ (5589831102429/12500000000000 : ℝ)^103 := by
    have hnat : (541172603 : ℕ)^135*12500000000000^103 ≤ 5589831102429^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541172603 1000000000 5589831102429 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245192567/10000000000 : ℝ)^135 ≤ (42923687976037/100000000000000 : ℝ)^103 := by
    have hnat : (5245192567 : ℕ)^135*100000000000000^103 ≤ 42923687976037^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245192567 10000000000 42923687976037 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014264149/5000000000 : ℝ), (541172603/1000000000 : ℝ), (5245192567/10000000000 : ℝ)] ![(12357663197333/100000000000000 : ℝ), (5589831102429/12500000000000 : ℝ), (42923687976037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014264149/5000000000 : ℝ)|^135 ≤ (12357663197333/100000000000000 : ℝ)^103
        have hw : |(-1014264149/5000000000 : ℝ)|=(1014264149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541172603/1000000000 : ℝ)|^135 ≤ (5589831102429/12500000000000 : ℝ)^103
        have hw : |(541172603/1000000000 : ℝ)|=(541172603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245192567/10000000000 : ℝ)|^135 ≤ (42923687976037/100000000000000 : ℝ)^103
        have hw : |(5245192567/10000000000 : ℝ)|=(5245192567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5348666817/10000000000 : ℝ)*x 0 + (-2113362577/10000000000 : ℝ)*x 1 + (40978067/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348666817/10000000000 : ℝ)^135 ≤ (44036924125291/100000000000000 : ℝ)^103 := by
    have hnat : (5348666817 : ℕ)^135*100000000000000^103 ≤ 44036924125291^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348666817 10000000000 44036924125291 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113362577/10000000000 : ℝ)^135 ≤ (13039387783823/100000000000000 : ℝ)^103 := by
    have hnat : (2113362577 : ℕ)^135*100000000000000^103 ≤ 13039387783823^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113362577 10000000000 13039387783823 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40978067/78125000 : ℝ)^135 ≤ (4292368807257/10000000000000 : ℝ)^103 := by
    have hnat : (40978067 : ℕ)^135*10000000000000^103 ≤ 4292368807257^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40978067 78125000 4292368807257 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348666817/10000000000 : ℝ), (-2113362577/10000000000 : ℝ), (40978067/78125000 : ℝ)] ![(44036924125291/100000000000000 : ℝ), (13039387783823/100000000000000 : ℝ), (4292368807257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348666817/10000000000 : ℝ)|^135 ≤ (44036924125291/100000000000000 : ℝ)^103
        have hw : |(5348666817/10000000000 : ℝ)|=(5348666817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113362577/10000000000 : ℝ)|^135 ≤ (13039387783823/100000000000000 : ℝ)^103
        have hw : |(-2113362577/10000000000 : ℝ)|=(2113362577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40978067/78125000 : ℝ)|^135 ≤ (4292368807257/10000000000000 : ℝ)^103
        have hw : |(40978067/78125000 : ℝ)|=(40978067/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2674333019/5000000000 : ℝ)*x 0 + (262259651/500000000 : ℝ)*x 1 + (-528340757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674333019/5000000000 : ℝ)^135 ≤ (44036915718981/100000000000000 : ℝ)^103 := by
    have hnat : (2674333019 : ℕ)^135*100000000000000^103 ≤ 44036915718981^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674333019 5000000000 44036915718981 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262259651/500000000 : ℝ)^135 ≤ (10730923208713/25000000000000 : ℝ)^103 := by
    have hnat : (262259651 : ℕ)^135*25000000000000^103 ≤ 10730923208713^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262259651 500000000 10730923208713 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528340757/2500000000 : ℝ)^135 ≤ (2607878286199/20000000000000 : ℝ)^103 := by
    have hnat : (528340757 : ℕ)^135*20000000000000^103 ≤ 2607878286199^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528340757 2500000000 2607878286199 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674333019/5000000000 : ℝ), (262259651/500000000 : ℝ), (-528340757/2500000000 : ℝ)] ![(44036915718981/100000000000000 : ℝ), (10730923208713/25000000000000 : ℝ), (2607878286199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674333019/5000000000 : ℝ)|^135 ≤ (44036915718981/100000000000000 : ℝ)^103
        have hw : |(2674333019/5000000000 : ℝ)|=(2674333019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262259651/500000000 : ℝ)|^135 ≤ (10730923208713/25000000000000 : ℝ)^103
        have hw : |(262259651/500000000 : ℝ)|=(262259651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528340757/2500000000 : ℝ)|^135 ≤ (2607878286199/20000000000000 : ℝ)^103
        have hw : |(-528340757/2500000000 : ℝ)|=(528340757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (864387577/2000000000 : ℝ)*x 0 + (4149654561/10000000000 : ℝ)*x 1 + (450083493/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864387577/2000000000 : ℝ)^135 ≤ (33303606405829/100000000000000 : ℝ)^103 := by
    have hnat : (864387577 : ℕ)^135*100000000000000^103 ≤ 33303606405829^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864387577 2000000000 33303606405829 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149654561/10000000000 : ℝ)^135 ≤ (31574468213107/100000000000000 : ℝ)^103 := by
    have hnat : (4149654561 : ℕ)^135*100000000000000^103 ≤ 31574468213107^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149654561 10000000000 31574468213107 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450083493/1000000000 : ℝ)^135 ≤ (7024385073121/20000000000000 : ℝ)^103 := by
    have hnat : (450083493 : ℕ)^135*20000000000000^103 ≤ 7024385073121^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450083493 1000000000 7024385073121 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864387577/2000000000 : ℝ), (4149654561/10000000000 : ℝ), (450083493/1000000000 : ℝ)] ![(33303606405829/100000000000000 : ℝ), (31574468213107/100000000000000 : ℝ), (7024385073121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864387577/2000000000 : ℝ)|^135 ≤ (33303606405829/100000000000000 : ℝ)^103
        have hw : |(864387577/2000000000 : ℝ)|=(864387577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149654561/10000000000 : ℝ)|^135 ≤ (31574468213107/100000000000000 : ℝ)^103
        have hw : |(4149654561/10000000000 : ℝ)|=(4149654561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450083493/1000000000 : ℝ)|^135 ≤ (7024385073121/20000000000000 : ℝ)^103
        have hw : |(450083493/1000000000 : ℝ)|=(450083493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014270053/5000000000 : ℝ)*x 0 + (2622894831/5000000000 : ℝ)*x 1 + (2705562989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014270053/5000000000 : ℝ)^135 ≤ (2471551495857/20000000000000 : ℝ)^103 := by
    have hnat : (1014270053 : ℕ)^135*20000000000000^103 ≤ 2471551495857^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014270053 5000000000 2471551495857 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622894831/5000000000 : ℝ)^135 ≤ (42930092446837/100000000000000 : ℝ)^103 := by
    have hnat : (2622894831 : ℕ)^135*100000000000000^103 ≤ 42930092446837^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622894831 5000000000 42930092446837 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705562989/5000000000 : ℝ)^135 ≤ (44712150054603/100000000000000 : ℝ)^103 := by
    have hnat : (2705562989 : ℕ)^135*100000000000000^103 ≤ 44712150054603^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705562989 5000000000 44712150054603 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014270053/5000000000 : ℝ), (2622894831/5000000000 : ℝ), (2705562989/5000000000 : ℝ)] ![(2471551495857/20000000000000 : ℝ), (42930092446837/100000000000000 : ℝ), (44712150054603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014270053/5000000000 : ℝ)|^135 ≤ (2471551495857/20000000000000 : ℝ)^103
        have hw : |(-1014270053/5000000000 : ℝ)|=(1014270053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622894831/5000000000 : ℝ)|^135 ≤ (42930092446837/100000000000000 : ℝ)^103
        have hw : |(2622894831/5000000000 : ℝ)|=(2622894831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705562989/5000000000 : ℝ)|^135 ≤ (44712150054603/100000000000000 : ℝ)^103
        have hw : |(2705562989/5000000000 : ℝ)|=(2705562989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305683293/10000000000 : ℝ)*x 0 + (676390797/1250000000 : ℝ)*x 1 + (-1947429569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305683293/10000000000 : ℝ)^135 ≤ (21786831160661/50000000000000 : ℝ)^103 := by
    have hnat : (5305683293 : ℕ)^135*50000000000000^103 ≤ 21786831160661^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305683293 10000000000 21786831160661 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676390797/1250000000 : ℝ)^135 ≤ (44712154365003/100000000000000 : ℝ)^103 := by
    have hnat : (676390797 : ℕ)^135*100000000000000^103 ≤ 44712154365003^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676390797 1250000000 44712154365003 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947429569/10000000000 : ℝ)^135 ≤ (11714183297773/100000000000000 : ℝ)^103 := by
    have hnat : (1947429569 : ℕ)^135*100000000000000^103 ≤ 11714183297773^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947429569 10000000000 11714183297773 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305683293/10000000000 : ℝ), (676390797/1250000000 : ℝ), (-1947429569/10000000000 : ℝ)] ![(21786831160661/50000000000000 : ℝ), (44712154365003/100000000000000 : ℝ), (11714183297773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305683293/10000000000 : ℝ)|^135 ≤ (21786831160661/50000000000000 : ℝ)^103
        have hw : |(5305683293/10000000000 : ℝ)|=(5305683293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676390797/1250000000 : ℝ)|^135 ≤ (44712154365003/100000000000000 : ℝ)^103
        have hw : |(676390797/1250000000 : ℝ)|=(676390797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947429569/10000000000 : ℝ)|^135 ≤ (11714183297773/100000000000000 : ℝ)^103
        have hw : |(-1947429569/10000000000 : ℝ)|=(1947429569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s9_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2160981707/5000000000 : ℝ)*x 0 + (2249788011/5000000000 : ℝ)*x 1 + (4150919677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160981707/5000000000 : ℝ)^135 ≤ (3330386424179/10000000000000 : ℝ)^103 := by
    have hnat : (2160981707 : ℕ)^135*10000000000000^103 ≤ 3330386424179^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160981707 5000000000 3330386424179 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249788011/5000000000 : ℝ)^135 ≤ (4388631259909/12500000000000 : ℝ)^103 := by
    have hnat : (2249788011 : ℕ)^135*12500000000000^103 ≤ 4388631259909^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249788011 5000000000 4388631259909 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150919677/10000000000 : ℝ)^135 ≤ (31587085662089/100000000000000 : ℝ)^103 := by
    have hnat : (4150919677 : ℕ)^135*100000000000000^103 ≤ 31587085662089^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150919677 10000000000 31587085662089 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160981707/5000000000 : ℝ), (2249788011/5000000000 : ℝ), (4150919677/10000000000 : ℝ)] ![(3330386424179/10000000000000 : ℝ), (4388631259909/12500000000000 : ℝ), (31587085662089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160981707/5000000000 : ℝ)|^135 ≤ (3330386424179/10000000000000 : ℝ)^103
        have hw : |(2160981707/5000000000 : ℝ)|=(2160981707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249788011/5000000000 : ℝ)|^135 ≤ (4388631259909/12500000000000 : ℝ)^103
        have hw : |(2249788011/5000000000 : ℝ)|=(2249788011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150919677/10000000000 : ℝ)|^135 ≤ (31587085662089/100000000000000 : ℝ)^103
        have hw : |(4150919677/10000000000 : ℝ)|=(4150919677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1399/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11191/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (973519136477431/10000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^4319 ≤ (973519136477431/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11191 : ℕ)^4319*10000000000000000000^1024 ≤ 973519136477431^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 973519136477431 10000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (973519136477431/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (482914595549423/1562500000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^4319 ≤ (482914595549423/1562500000000000000 : ℝ)^1024 := by
      have hnat : (14717 : ℕ)^4319*1562500000000000000^1024 ≤ 482914595549423^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 482914595549423 1562500000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (482914595549423/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000973519136477431/5000000000000000000 : ℝ) ≤ (10000461592759953/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (5000973519136477431/5000000000000000000 : ℝ)^1024 ≤ (10000461592759953/10000000000000000 : ℝ)^4319 := by
      have hnat : (5000973519136477431 : ℕ)^1024*10000000000000000^4319 ≤ 10000461592759953^4319*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000973519136477431 5000000000000000000 10000461592759953 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000461592759953/10000000000000000 : ℝ)) (X := (5000973519136477431/5000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020320862739968691/50000000000000000000 : ℝ) ≤ (2500240858280559/2500000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50020320862739968691/50000000000000000000 : ℝ)^1024 ≤ (2500240858280559/2500000000000000 : ℝ)^4319 := by
      have hnat : (50020320862739968691 : ℕ)^1024*2500000000000000^4319 ≤ 2500240858280559^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020320862739968691 50000000000000000000 2500240858280559 2500000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500240858280559/2500000000000000 : ℝ)) (X := (50020320862739968691/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781732914595549423/781250000000000000 : ℝ) ≤ (10001465273484519/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (781732914595549423/781250000000000000 : ℝ)^1024 ≤ (10001465273484519/10000000000000000 : ℝ)^4319 := by
      have hnat : (781732914595549423 : ℕ)^1024*10000000000000000^4319 ≤ 10001465273484519^4319*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781732914595549423 781250000000000000 10001465273484519 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001465273484519/10000000000000000 : ℝ)) (X := (781732914595549423/781250000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(973519136477431/10000000000000000000 : ℝ) ≤ ((8812598846270744043/8815000000000000000 : ℝ)+2*(501840362283/352600000000000 : ℝ)*(11191/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (8812598846270744043/8815000000000000000 : ℝ)+2*(501840362283/352600000000000 : ℝ)*(11191/100000 : ℝ)=(10000461592759953/10000000000000000 : ℝ) by norm_num, show 1+2*(973519136477431/10000000000000000000 : ℝ)=(5000973519136477431/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(482914595549423/1562500000000000000 : ℝ)+(973519136477431/10000000000000000000 : ℝ) ≤ ((8812598846270744043/8815000000000000000 : ℝ)+(501840362283/352600000000000 : ℝ)*((14717/100000 : ℝ)+(11191/100000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (8812598846270744043/8815000000000000000 : ℝ)+(501840362283/352600000000000 : ℝ)*((14717/100000 : ℝ)+(11191/100000 : ℝ))=(2500240858280559/2500000000000000 : ℝ) by norm_num, show 1+(482914595549423/1562500000000000000 : ℝ)+(973519136477431/10000000000000000000 : ℝ)=(50020320862739968691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(482914595549423/1562500000000000000 : ℝ) ≤ ((8812598846270744043/8815000000000000000 : ℝ)+2*(501840362283/352600000000000 : ℝ)*(14717/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (8812598846270744043/8815000000000000000 : ℝ)+2*(501840362283/352600000000000 : ℝ)*(14717/100000 : ℝ)=(10001465273484519/10000000000000000 : ℝ) by norm_num, show 1+2*(482914595549423/1562500000000000000 : ℝ)=(781732914595549423/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8812598846270744043/8815000000000000000 : ℝ)*(X 1 0+X 2 0)+(501840362283/352600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (8812598846270744043/8815000000000000000 : ℝ)) (alpha := (501840362283/352600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8812598846270744043/8815000000000000000 : ℝ)*(X 0 1+X 2 1)+(501840362283/352600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (8812598846270744043/8815000000000000000 : ℝ)) (alpha := (501840362283/352600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8812598846270744043/8815000000000000000 : ℝ)*(X 0 2+X 1 2)+(501840362283/352600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (8812598846270744043/8815000000000000000 : ℝ)) (alpha := (501840362283/352600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1014264149/5000000000 : ℝ)*X 0 0+(541172603/1000000000 : ℝ)*X 0 1+(5245192567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348666817/10000000000 : ℝ)*X 1 0+(-2113362577/10000000000 : ℝ)*X 1 1+(40978067/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674333019/5000000000 : ℝ)*X 2 0+(262259651/500000000 : ℝ)*X 2 1+(-528340757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864387577/2000000000 : ℝ)*X 0 0+(4149654561/10000000000 : ℝ)*X 0 1+(450083493/1000000000 : ℝ)*X 0 2+(864387577/2000000000 : ℝ)*X 1 0+(4149654561/10000000000 : ℝ)*X 1 1+(450083493/1000000000 : ℝ)*X 1 2+(864387577/2000000000 : ℝ)*X 2 0+(4149654561/10000000000 : ℝ)*X 2 1+(450083493/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1014270053/5000000000 : ℝ)*X 0 0+(2622894831/5000000000 : ℝ)*X 0 1+(2705562989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305683293/10000000000 : ℝ)*X 2 0+(676390797/1250000000 : ℝ)*X 2 1+(-1947429569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2160981707/5000000000 : ℝ)*X 0 0+(2249788011/5000000000 : ℝ)*X 0 1+(4150919677/10000000000 : ℝ)*X 0 2+(2160981707/5000000000 : ℝ)*X 1 0+(2249788011/5000000000 : ℝ)*X 1 1+(4150919677/10000000000 : ℝ)*X 1 2+(2160981707/5000000000 : ℝ)*X 2 0+(2249788011/5000000000 : ℝ)*X 2 1+(4150919677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5277910788313831021368189/5375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1178950771/100000000000000 : ℝ)*(base19) + (31287037/12500000000000 : ℝ)*(base23) + (3940897/10000000000000 : ℝ)*(upper2) + (140940287/100000000000000 : ℝ)*(upper3) + (2213108998210927/50000000000000 : ℝ)*(major0) + (2213108998210927/50000000000000 : ℝ)*(major1) + (2213108998210927/50000000000000 : ℝ)*(major2) + (3002419198845227/50000000000000 : ℝ)*(sp0) + (1200972566676167/20000000000000 : ℝ)*(sp1) + (6004847863464749/100000000000000 : ℝ)*(sp2) + (1423778297738253/50000000000000 : ℝ)*(sp3) + (12507149/48828125000 : ℝ)*(sp4) + (15898570561/100000000000000 : ℝ)*(sp5) + (15352304359/100000000000000 : ℝ)*(sp6) + (1423785973890433/50000000000000 : ℝ)*(f.failure) + (3002432006165803/50000000000000 : ℝ)*(f.sum) + (20050457421/215000000000000000000000000 : ℝ)*base65 + (2603619212797979/10750000000000000000000000000000 : ℝ)*base68 + (117900773619547979/10750000000000000000000000000000 : ℝ)*base70 + (9325504160047979/10750000000000000000000000000000 : ℝ)*base72 + (168085710483/107500000000000000000000000 : ℝ)*base73 + (189925546644047979/10750000000000000000000000000000 : ℝ)*base76 + (9084485290047979/10750000000000000000000000000000 : ℝ)*base78 + (56346961436797979/10750000000000000000000000000000 : ℝ)*base80 + (353375820729/215000000000000000000000000 : ℝ)*base82 + (869907/62500000000000000000 : ℝ)*base89 + (869907/62500000000000000000 : ℝ)*base91 + (869907/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1360_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_box_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-232836831/1250000000 : ℝ)*x 0 + (5389182601/10000000000 : ℝ)*x 1 + (5389183159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232836831/1250000000 : ℝ)^135 ≤ (11050694253709/100000000000000 : ℝ)^103 := by
    have hnat : (232836831 : ℕ)^135*100000000000000^103 ≤ 11050694253709^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232836831 1250000000 11050694253709 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389182601/10000000000 : ℝ)^135 ≤ (44474649845289/100000000000000 : ℝ)^103 := by
    have hnat : (5389182601 : ℕ)^135*100000000000000^103 ≤ 44474649845289^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389182601 10000000000 44474649845289 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389183159/10000000000 : ℝ)^135 ≤ (5559331985111/12500000000000 : ℝ)^103 := by
    have hnat : (5389183159 : ℕ)^135*12500000000000^103 ≤ 5559331985111^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389183159 10000000000 5559331985111 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232836831/1250000000 : ℝ), (5389182601/10000000000 : ℝ), (5389183159/10000000000 : ℝ)] ![(11050694253709/100000000000000 : ℝ), (44474649845289/100000000000000 : ℝ), (5559331985111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232836831/1250000000 : ℝ)|^135 ≤ (11050694253709/100000000000000 : ℝ)^103
        have hw : |(-232836831/1250000000 : ℝ)|=(232836831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389182601/10000000000 : ℝ)|^135 ≤ (44474649845289/100000000000000 : ℝ)^103
        have hw : |(5389182601/10000000000 : ℝ)|=(5389182601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389183159/10000000000 : ℝ)|^135 ≤ (5559331985111/12500000000000 : ℝ)^103
        have hw : |(5389183159/10000000000 : ℝ)|=(5389183159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (264270063/500000000 : ℝ)*x 0 + (-2004967089/10000000000 : ℝ)*x 1 + (1077836509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264270063/500000000 : ℝ)^135 ≤ (867109469213/2000000000000 : ℝ)^103 := by
    have hnat : (264270063 : ℕ)^135*2000000000000^103 ≤ 867109469213^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264270063 500000000 867109469213 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004967089/10000000000 : ℝ)^135 ≤ (12169877286047/100000000000000 : ℝ)^103 := by
    have hnat : (2004967089 : ℕ)^135*100000000000000^103 ≤ 12169877286047^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004967089 10000000000 12169877286047 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077836509/2000000000 : ℝ)^135 ≤ (8894929847913/20000000000000 : ℝ)^103 := by
    have hnat : (1077836509 : ℕ)^135*20000000000000^103 ≤ 8894929847913^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077836509 2000000000 8894929847913 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264270063/500000000 : ℝ), (-2004967089/10000000000 : ℝ), (1077836509/2000000000 : ℝ)] ![(867109469213/2000000000000 : ℝ), (12169877286047/100000000000000 : ℝ), (8894929847913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264270063/500000000 : ℝ)|^135 ≤ (867109469213/2000000000000 : ℝ)^103
        have hw : |(264270063/500000000 : ℝ)|=(264270063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004967089/10000000000 : ℝ)|^135 ≤ (12169877286047/100000000000000 : ℝ)^103
        have hw : |(-2004967089/10000000000 : ℝ)|=(2004967089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077836509/2000000000 : ℝ)|^135 ≤ (8894929847913/20000000000000 : ℝ)^103
        have hw : |(1077836509/2000000000 : ℝ)|=(1077836509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1057080217/2000000000 : ℝ)*x 0 + (336823919/625000000 : ℝ)*x 1 + (-2004967109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057080217/2000000000 : ℝ)^135 ≤ (21677735789583/50000000000000 : ℝ)^103 := by
    have hnat : (1057080217 : ℕ)^135*50000000000000^103 ≤ 21677735789583^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057080217 2000000000 21677735789583 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336823919/625000000 : ℝ)^135 ≤ (44474650959387/100000000000000 : ℝ)^103 := by
    have hnat : (336823919 : ℕ)^135*100000000000000^103 ≤ 44474650959387^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336823919 625000000 44474650959387 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004967109/10000000000 : ℝ)^135 ≤ (304246936129/2500000000000 : ℝ)^103 := by
    have hnat : (2004967109 : ℕ)^135*2500000000000^103 ≤ 304246936129^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004967109 10000000000 304246936129 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057080217/2000000000 : ℝ), (336823919/625000000 : ℝ), (-2004967109/10000000000 : ℝ)] ![(21677735789583/50000000000000 : ℝ), (44474650959387/100000000000000 : ℝ), (304246936129/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057080217/2000000000 : ℝ)|^135 ≤ (21677735789583/50000000000000 : ℝ)^103
        have hw : |(1057080217/2000000000 : ℝ)|=(1057080217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336823919/625000000 : ℝ)|^135 ≤ (44474650959387/100000000000000 : ℝ)^103
        have hw : |(336823919/625000000 : ℝ)|=(336823919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2004967109/10000000000 : ℝ)|^135 ≤ (304246936129/2500000000000 : ℝ)^103
        have hw : |(-2004967109/10000000000 : ℝ)|=(2004967109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4469703293/10000000000 : ℝ)*x 0 + (4251903793/10000000000 : ℝ)*x 1 + (4251903991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469703293/10000000000 : ℝ)^135 ≤ (34803860203577/100000000000000 : ℝ)^103 := by
    have hnat : (4469703293 : ℕ)^135*100000000000000^103 ≤ 34803860203577^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469703293 10000000000 34803860203577 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251903793/10000000000 : ℝ)^135 ≤ (4074758612093/12500000000000 : ℝ)^103 := by
    have hnat : (4251903793 : ℕ)^135*12500000000000^103 ≤ 4074758612093^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251903793 10000000000 4074758612093 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251903991/10000000000 : ℝ)^135 ≤ (8149517721591/25000000000000 : ℝ)^103 := by
    have hnat : (4251903991 : ℕ)^135*25000000000000^103 ≤ 8149517721591^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251903991 10000000000 8149517721591 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469703293/10000000000 : ℝ), (4251903793/10000000000 : ℝ), (4251903991/10000000000 : ℝ)] ![(34803860203577/100000000000000 : ℝ), (4074758612093/12500000000000 : ℝ), (8149517721591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469703293/10000000000 : ℝ)|^135 ≤ (34803860203577/100000000000000 : ℝ)^103
        have hw : |(4469703293/10000000000 : ℝ)|=(4469703293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251903793/10000000000 : ℝ)|^135 ≤ (4074758612093/12500000000000 : ℝ)^103
        have hw : |(4251903793/10000000000 : ℝ)|=(4251903793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251903991/10000000000 : ℝ)|^135 ≤ (8149517721591/25000000000000 : ℝ)^103
        have hw : |(4251903991/10000000000 : ℝ)|=(4251903991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-219710359/1000000000 : ℝ)*x 0 + (5265314101/10000000000 : ℝ)*x 1 + (5265314581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219710359/1000000000 : ℝ)^135 ≤ (6860360179721/50000000000000 : ℝ)^103 := by
    have hnat : (219710359 : ℕ)^135*50000000000000^103 ≤ 6860360179721^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219710359 1000000000 6860360179721 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265314101/10000000000 : ℝ)^135 ≤ (43139637235699/100000000000000 : ℝ)^103 := by
    have hnat : (5265314101 : ℕ)^135*100000000000000^103 ≤ 43139637235699^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265314101 10000000000 43139637235699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265314581/10000000000 : ℝ)^135 ≤ (269622764939/625000000000 : ℝ)^103 := by
    have hnat : (5265314581 : ℕ)^135*625000000000^103 ≤ 269622764939^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265314581 10000000000 269622764939 625000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219710359/1000000000 : ℝ), (5265314101/10000000000 : ℝ), (5265314581/10000000000 : ℝ)] ![(6860360179721/50000000000000 : ℝ), (43139637235699/100000000000000 : ℝ), (269622764939/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219710359/1000000000 : ℝ)|^135 ≤ (6860360179721/50000000000000 : ℝ)^103
        have hw : |(-219710359/1000000000 : ℝ)|=(219710359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265314101/10000000000 : ℝ)|^135 ≤ (43139637235699/100000000000000 : ℝ)^103
        have hw : |(5265314101/10000000000 : ℝ)|=(5265314101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265314581/10000000000 : ℝ)|^135 ≤ (269622764939/625000000000 : ℝ)^103
        have hw : |(5265314581/10000000000 : ℝ)|=(5265314581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5372337489/10000000000 : ℝ)*x 0 + (-1027398119/5000000000 : ℝ)*x 1 + (5265314761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372337489/10000000000 : ℝ)^135 ≤ (44292533464627/100000000000000 : ℝ)^103 := by
    have hnat : (5372337489 : ℕ)^135*100000000000000^103 ≤ 44292533464627^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372337489 10000000000 44292533464627 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027398119/5000000000 : ℝ)^135 ≤ (12567822193209/100000000000000 : ℝ)^103 := by
    have hnat : (1027398119 : ℕ)^135*100000000000000^103 ≤ 12567822193209^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027398119 5000000000 12567822193209 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265314761/10000000000 : ℝ)^135 ≤ (43139644323193/100000000000000 : ℝ)^103 := by
    have hnat : (5265314761 : ℕ)^135*100000000000000^103 ≤ 43139644323193^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265314761 10000000000 43139644323193 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372337489/10000000000 : ℝ), (-1027398119/5000000000 : ℝ), (5265314761/10000000000 : ℝ)] ![(44292533464627/100000000000000 : ℝ), (12567822193209/100000000000000 : ℝ), (43139644323193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372337489/10000000000 : ℝ)|^135 ≤ (44292533464627/100000000000000 : ℝ)^103
        have hw : |(5372337489/10000000000 : ℝ)|=(5372337489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1027398119/5000000000 : ℝ)|^135 ≤ (12567822193209/100000000000000 : ℝ)^103
        have hw : |(-1027398119/5000000000 : ℝ)|=(1027398119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265314761/10000000000 : ℝ)|^135 ≤ (43139644323193/100000000000000 : ℝ)^103
        have hw : |(5265314761/10000000000 : ℝ)|=(5265314761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1343084341/2500000000 : ℝ)*x 0 + (263265743/500000000 : ℝ)*x 1 + (-1027398137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343084341/2500000000 : ℝ)^135 ≤ (1107313302847/2500000000000 : ℝ)^103 := by
    have hnat : (1343084341 : ℕ)^135*2500000000000^103 ≤ 1107313302847^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343084341 2500000000 1107313302847 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263265743/500000000 : ℝ)^135 ≤ (43139645386317/100000000000000 : ℝ)^103 := by
    have hnat : (263265743 : ℕ)^135*100000000000000^103 ≤ 43139645386317^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263265743 500000000 43139645386317 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027398137/5000000000 : ℝ)^135 ≤ (2513564496361/20000000000000 : ℝ)^103 := by
    have hnat : (1027398137 : ℕ)^135*20000000000000^103 ≤ 2513564496361^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027398137 5000000000 2513564496361 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343084341/2500000000 : ℝ), (263265743/500000000 : ℝ), (-1027398137/5000000000 : ℝ)] ![(1107313302847/2500000000000 : ℝ), (43139645386317/100000000000000 : ℝ), (2513564496361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343084341/2500000000 : ℝ)|^135 ≤ (1107313302847/2500000000000 : ℝ)^103
        have hw : |(1343084341/2500000000 : ℝ)|=(1343084341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263265743/500000000 : ℝ)|^135 ≤ (43139645386317/100000000000000 : ℝ)^103
        have hw : |(263265743/500000000 : ℝ)|=(263265743/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1027398137/5000000000 : ℝ)|^135 ≤ (2513564496361/20000000000000 : ℝ)^103
        have hw : |(-1027398137/5000000000 : ℝ)|=(1027398137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4173220319/10000000000 : ℝ)*x 0 + (4400092281/10000000000 : ℝ)*x 1 + (4400092503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173220319/10000000000 : ℝ)^135 ≤ (7952423443281/25000000000000 : ℝ)^103 := by
    have hnat : (4173220319 : ℕ)^135*25000000000000^103 ≤ 7952423443281^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173220319 10000000000 7952423443281 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4400092281/10000000000 : ℝ)^135 ≤ (8523787993777/25000000000000 : ℝ)^103 := by
    have hnat : (4400092281 : ℕ)^135*25000000000000^103 ≤ 8523787993777^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400092281 10000000000 8523787993777 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4400092503/10000000000 : ℝ)^135 ≤ (8523788557441/25000000000000 : ℝ)^103 := by
    have hnat : (4400092503 : ℕ)^135*25000000000000^103 ≤ 8523788557441^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400092503 10000000000 8523788557441 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173220319/10000000000 : ℝ), (4400092281/10000000000 : ℝ), (4400092503/10000000000 : ℝ)] ![(7952423443281/25000000000000 : ℝ), (8523787993777/25000000000000 : ℝ), (8523788557441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173220319/10000000000 : ℝ)|^135 ≤ (7952423443281/25000000000000 : ℝ)^103
        have hw : |(4173220319/10000000000 : ℝ)|=(4173220319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4400092281/10000000000 : ℝ)|^135 ≤ (8523787993777/25000000000000 : ℝ)^103
        have hw : |(4400092281/10000000000 : ℝ)|=(4400092281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4400092503/10000000000 : ℝ)|^135 ≤ (8523788557441/25000000000000 : ℝ)^103
        have hw : |(4400092503/10000000000 : ℝ)|=(4400092503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_8 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126831063/10000000000 : ℝ)*x 0 + (2589977931/5000000000 : ℝ)*x 1 + (84424903/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126831063/10000000000 : ℝ)^135 ≤ (6574206582707/50000000000000 : ℝ)^103 := by
    have hnat : (2126831063 : ℕ)^135*50000000000000^103 ≤ 6574206582707^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126831063 10000000000 6574206582707 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589977931/5000000000 : ℝ)^135 ≤ (21112661976987/50000000000000 : ℝ)^103 := by
    have hnat : (2589977931 : ℕ)^135*50000000000000^103 ≤ 21112661976987^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589977931 5000000000 21112661976987 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84424903/156250000 : ℝ)^135 ≤ (44626262862807/100000000000000 : ℝ)^103 := by
    have hnat : (84424903 : ℕ)^135*100000000000000^103 ≤ 44626262862807^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84424903 156250000 44626262862807 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126831063/10000000000 : ℝ), (2589977931/5000000000 : ℝ), (84424903/156250000 : ℝ)] ![(6574206582707/50000000000000 : ℝ), (21112661976987/50000000000000 : ℝ), (44626262862807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126831063/10000000000 : ℝ)|^135 ≤ (6574206582707/50000000000000 : ℝ)^103
        have hw : |(-2126831063/10000000000 : ℝ)|=(2126831063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589977931/5000000000 : ℝ)|^135 ≤ (21112661976987/50000000000000 : ℝ)^103
        have hw : |(2589977931/5000000000 : ℝ)|=(2589977931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84424903/156250000 : ℝ)|^135 ≤ (44626262862807/100000000000000 : ℝ)^103
        have hw : |(84424903/156250000 : ℝ)|=(84424903/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_9 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5275562111/10000000000 : ℝ)*x 0 + (-999599819/5000000000 : ℝ)*x 1 + (1350798519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275562111/10000000000 : ℝ)^135 ≤ (8649944009593/20000000000000 : ℝ)^103 := by
    have hnat : (5275562111 : ℕ)^135*20000000000000^103 ≤ 8649944009593^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275562111 10000000000 8649944009593 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999599819/5000000000 : ℝ)^135 ≤ (2424802799901/20000000000000 : ℝ)^103 := by
    have hnat : (999599819 : ℕ)^135*20000000000000^103 ≤ 2424802799901^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999599819 5000000000 2424802799901 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350798519/2500000000 : ℝ)^135 ≤ (2789141621073/6250000000000 : ℝ)^103 := by
    have hnat : (1350798519 : ℕ)^135*6250000000000^103 ≤ 2789141621073^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350798519 2500000000 2789141621073 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275562111/10000000000 : ℝ), (-999599819/5000000000 : ℝ), (1350798519/2500000000 : ℝ)] ![(8649944009593/20000000000000 : ℝ), (2424802799901/20000000000000 : ℝ), (2789141621073/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275562111/10000000000 : ℝ)|^135 ≤ (8649944009593/20000000000000 : ℝ)^103
        have hw : |(5275562111/10000000000 : ℝ)|=(5275562111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999599819/5000000000 : ℝ)|^135 ≤ (2424802799901/20000000000000 : ℝ)^103
        have hw : |(-999599819/5000000000 : ℝ)|=(999599819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350798519/2500000000 : ℝ)|^135 ≤ (2789141621073/6250000000000 : ℝ)^103
        have hw : |(1350798519/2500000000 : ℝ)|=(1350798519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_10 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2637781209/5000000000 : ℝ)*x 0 + (1350798481/2500000000 : ℝ)*x 1 + (-1999199431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637781209/5000000000 : ℝ)^135 ≤ (8649944669343/20000000000000 : ℝ)^103 := by
    have hnat : (2637781209 : ℕ)^135*20000000000000^103 ≤ 8649944669343^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637781209 5000000000 8649944669343 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350798481/2500000000 : ℝ)^135 ≤ (5578283036467/12500000000000 : ℝ)^103 := by
    have hnat : (1350798481 : ℕ)^135*12500000000000^103 ≤ 5578283036467^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350798481 2500000000 5578283036467 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999199431/10000000000 : ℝ)^135 ≤ (12124012354159/100000000000000 : ℝ)^103 := by
    have hnat : (1999199431 : ℕ)^135*100000000000000^103 ≤ 12124012354159^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999199431 10000000000 12124012354159 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637781209/5000000000 : ℝ), (1350798481/2500000000 : ℝ), (-1999199431/10000000000 : ℝ)] ![(8649944669343/20000000000000 : ℝ), (5578283036467/12500000000000 : ℝ), (12124012354159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637781209/5000000000 : ℝ)|^135 ≤ (8649944669343/20000000000000 : ℝ)^103
        have hw : |(2637781209/5000000000 : ℝ)|=(2637781209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350798481/2500000000 : ℝ)|^135 ≤ (5578283036467/12500000000000 : ℝ)^103
        have hw : |(1350798481/2500000000 : ℝ)|=(1350798481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999199431/10000000000 : ℝ)|^135 ≤ (12124012354159/100000000000000 : ℝ)^103
        have hw : |(-1999199431/10000000000 : ℝ)|=(1999199431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_11 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1125670063/2500000000 : ℝ)*x 0 + (66173881/156250000 : ℝ)*x 1 + (2117563871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125670063/2500000000 : ℝ)^135 ≤ (7028160026439/20000000000000 : ℝ)^103 := by
    have hnat : (1125670063 : ℕ)^135*20000000000000^103 ≤ 7028160026439^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125670063 2500000000 7028160026439 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66173881/156250000 : ℝ)^135 ≤ (32429603149249/100000000000000 : ℝ)^103 := by
    have hnat : (66173881 : ℕ)^135*100000000000000^103 ≤ 32429603149249^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66173881 156250000 32429603149249 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117563871/5000000000 : ℝ)^135 ≤ (1297183868239/4000000000000 : ℝ)^103 := by
    have hnat : (2117563871 : ℕ)^135*4000000000000^103 ≤ 1297183868239^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117563871 5000000000 1297183868239 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125670063/2500000000 : ℝ), (66173881/156250000 : ℝ), (2117563871/5000000000 : ℝ)] ![(7028160026439/20000000000000 : ℝ), (32429603149249/100000000000000 : ℝ), (1297183868239/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125670063/2500000000 : ℝ)|^135 ≤ (7028160026439/20000000000000 : ℝ)^103
        have hw : |(1125670063/2500000000 : ℝ)|=(1125670063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66173881/156250000 : ℝ)|^135 ≤ (32429603149249/100000000000000 : ℝ)^103
        have hw : |(66173881/156250000 : ℝ)|=(66173881/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117563871/5000000000 : ℝ)|^135 ≤ (1297183868239/4000000000000 : ℝ)^103
        have hw : |(2117563871/5000000000 : ℝ)|=(2117563871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_12 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-120829321/625000000 : ℝ)*x 0 + (5472376653/10000000000 : ℝ)*x 1 + (656778933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120829321/625000000 : ℝ)^135 ≤ (5801334354899/50000000000000 : ℝ)^103 := by
    have hnat : (120829321 : ℕ)^135*50000000000000^103 ≤ 5801334354899^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120829321 625000000 5801334354899 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472376653/10000000000 : ℝ)^135 ≤ (9075333482927/20000000000000 : ℝ)^103 := by
    have hnat : (5472376653 : ℕ)^135*20000000000000^103 ≤ 9075333482927^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472376653 10000000000 9075333482927 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656778933/1250000000 : ℝ)^135 ≤ (21510331932503/50000000000000 : ℝ)^103 := by
    have hnat : (656778933 : ℕ)^135*50000000000000^103 ≤ 21510331932503^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656778933 1250000000 21510331932503 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120829321/625000000 : ℝ), (5472376653/10000000000 : ℝ), (656778933/1250000000 : ℝ)] ![(5801334354899/50000000000000 : ℝ), (9075333482927/20000000000000 : ℝ), (21510331932503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120829321/625000000 : ℝ)|^135 ≤ (5801334354899/50000000000000 : ℝ)^103
        have hw : |(-120829321/625000000 : ℝ)|=(120829321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472376653/10000000000 : ℝ)|^135 ≤ (9075333482927/20000000000000 : ℝ)^103
        have hw : |(5472376653/10000000000 : ℝ)|=(5472376653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656778933/1250000000 : ℝ)|^135 ≤ (21510331932503/50000000000000 : ℝ)^103
        have hw : |(656778933/1250000000 : ℝ)|=(656778933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_13 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5380114149/10000000000 : ℝ)*x 0 + (-1029575957/5000000000 : ℝ)*x 1 + (5254231297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380114149/10000000000 : ℝ)^135 ≤ (44376586713077/100000000000000 : ℝ)^103 := by
    have hnat : (5380114149 : ℕ)^135*100000000000000^103 ≤ 44376586713077^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380114149 10000000000 44376586713077 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029575957/5000000000 : ℝ)^135 ≤ (3150687801061/25000000000000 : ℝ)^103 := by
    have hnat : (1029575957 : ℕ)^135*25000000000000^103 ≤ 3150687801061^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029575957 5000000000 3150687801061 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254231297/10000000000 : ℝ)^135 ≤ (43020662072829/100000000000000 : ℝ)^103 := by
    have hnat : (5254231297 : ℕ)^135*100000000000000^103 ≤ 43020662072829^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254231297 10000000000 43020662072829 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380114149/10000000000 : ℝ), (-1029575957/5000000000 : ℝ), (5254231297/10000000000 : ℝ)] ![(44376586713077/100000000000000 : ℝ), (3150687801061/25000000000000 : ℝ), (43020662072829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380114149/10000000000 : ℝ)|^135 ≤ (44376586713077/100000000000000 : ℝ)^103
        have hw : |(5380114149/10000000000 : ℝ)|=(5380114149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029575957/5000000000 : ℝ)|^135 ≤ (3150687801061/25000000000000 : ℝ)^103
        have hw : |(-1029575957/5000000000 : ℝ)|=(1029575957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254231297/10000000000 : ℝ)|^135 ≤ (43020662072829/100000000000000 : ℝ)^103
        have hw : |(5254231297/10000000000 : ℝ)|=(5254231297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_14 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2690057087/5000000000 : ℝ)*x 0 + (5254231353/10000000000 : ℝ)*x 1 + (-411830361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690057087/5000000000 : ℝ)^135 ≤ (44376586983347/100000000000000 : ℝ)^103 := by
    have hnat : (2690057087 : ℕ)^135*100000000000000^103 ≤ 44376586983347^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690057087 5000000000 44376586983347 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254231353/10000000000 : ℝ)^135 ≤ (21510331336899/50000000000000 : ℝ)^103 := by
    have hnat : (5254231353 : ℕ)^135*50000000000000^103 ≤ 21510331336899^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254231353 10000000000 21510331336899 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411830361/2000000000 : ℝ)^135 ≤ (1575343791233/12500000000000 : ℝ)^103 := by
    have hnat : (411830361 : ℕ)^135*12500000000000^103 ≤ 1575343791233^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411830361 2000000000 1575343791233 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690057087/5000000000 : ℝ), (5254231353/10000000000 : ℝ), (-411830361/2000000000 : ℝ)] ![(44376586983347/100000000000000 : ℝ), (21510331336899/50000000000000 : ℝ), (1575343791233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690057087/5000000000 : ℝ)|^135 ≤ (44376586983347/100000000000000 : ℝ)^103
        have hw : |(2690057087/5000000000 : ℝ)|=(2690057087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254231353/10000000000 : ℝ)|^135 ≤ (21510331336899/50000000000000 : ℝ)^103
        have hw : |(5254231353/10000000000 : ℝ)|=(5254231353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411830361/2000000000 : ℝ)|^135 ≤ (1575343791233/12500000000000 : ℝ)^103
        have hw : |(-411830361/2000000000 : ℝ)|=(411830361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_box_15 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1036561127/2500000000 : ℝ)*x 0 + (2206670679/5000000000 : ℝ)*x 1 + (551667517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036561127/2500000000 : ℝ)^135 ≤ (15770232250947/50000000000000 : ℝ)^103 := by
    have hnat : (1036561127 : ℕ)^135*50000000000000^103 ≤ 15770232250947^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036561127 2500000000 15770232250947 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206670679/5000000000 : ℝ)^135 ≤ (34229773951989/100000000000000 : ℝ)^103 := by
    have hnat : (2206670679 : ℕ)^135*100000000000000^103 ≤ 34229773951989^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206670679 5000000000 34229773951989 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551667517/1250000000 : ℝ)^135 ≤ (273838092237/800000000000 : ℝ)^103 := by
    have hnat : (551667517 : ℕ)^135*800000000000^103 ≤ 273838092237^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551667517 1250000000 273838092237 800000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036561127/2500000000 : ℝ), (2206670679/5000000000 : ℝ), (551667517/1250000000 : ℝ)] ![(15770232250947/50000000000000 : ℝ), (34229773951989/100000000000000 : ℝ), (273838092237/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036561127/2500000000 : ℝ)|^135 ≤ (15770232250947/50000000000000 : ℝ)^103
        have hw : |(1036561127/2500000000 : ℝ)|=(1036561127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2206670679/5000000000 : ℝ)|^135 ≤ (34229773951989/100000000000000 : ℝ)^103
        have hw : |(2206670679/5000000000 : ℝ)|=(2206670679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551667517/1250000000 : ℝ)|^135 ≤ (273838092237/800000000000 : ℝ)^103
        have hw : |(551667517/1250000000 : ℝ)|=(551667517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62863/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1843/3125 : ℝ) ∧ (80059/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42211/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1399/12500 : ℝ) ^ (4319/1024 : ℝ) ≤ (9738860986353613/100000000000000000000 : ℝ) := by
    have hpowers : (1399/12500 : ℝ)^4319 ≤ (9738860986353613/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1399 : ℕ)^4319*100000000000000000000^1024 ≤ 9738860986353613^1024*12500^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 12500 9738860986353613 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/12500 : ℝ)) (X := (9738860986353613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (4319/1024 : ℝ) ≤ (482914595549423/1562500000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^4319 ≤ (482914595549423/1562500000000000000 : ℝ)^1024 := by
      have hnat : (14717 : ℕ)^4319*1562500000000000000^1024 ≤ 482914595549423^1024*100000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 482914595549423 1562500000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (482914595549423/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009738860986353613/50000000000000000000 : ℝ) ≤ (10000461766741631/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50009738860986353613/50000000000000000000 : ℝ)^1024 ≤ (10000461766741631/10000000000000000 : ℝ)^4319 := by
      have hnat : (50009738860986353613 : ℕ)^1024*10000000000000000^4319 ≤ 10000461766741631^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009738860986353613 50000000000000000000 10000461766741631 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000461766741631/10000000000000000 : ℝ)) (X := (50009738860986353613/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008129079020303337/20000000000000000000 : ℝ) ≤ (10000963520099031/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (20008129079020303337/20000000000000000000 : ℝ)^1024 ≤ (10000963520099031/10000000000000000 : ℝ)^4319 := by
      have hnat : (20008129079020303337 : ℕ)^1024*10000000000000000^4319 ≤ 10000963520099031^4319*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008129079020303337 20000000000000000000 10000963520099031 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000963520099031/10000000000000000 : ℝ)) (X := (20008129079020303337/20000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781732914595549423/781250000000000000 : ℝ) ≤ (10001465273456431/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (781732914595549423/781250000000000000 : ℝ)^1024 ≤ (10001465273456431/10000000000000000 : ℝ)^4319 := by
      have hnat : (781732914595549423 : ℕ)^1024*10000000000000000^4319 ≤ 10001465273456431^4319*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781732914595549423 781250000000000000 10001465273456431 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001465273456431/10000000000000000 : ℝ)) (X := (781732914595549423/781250000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9738860986353613/100000000000000000000 : ℝ) ≤ ((1409615859224488307/1410000000000000000 : ℝ)+2*(2508766787/1762500000000 : ℝ)*(1399/12500 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (1409615859224488307/1410000000000000000 : ℝ)+2*(2508766787/1762500000000 : ℝ)*(1399/12500 : ℝ)=(10000461766741631/10000000000000000 : ℝ) by norm_num, show 1+2*(9738860986353613/100000000000000000000 : ℝ)=(50009738860986353613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(482914595549423/1562500000000000000 : ℝ)+(9738860986353613/100000000000000000000 : ℝ) ≤ ((1409615859224488307/1410000000000000000 : ℝ)+(2508766787/1762500000000 : ℝ)*((14717/100000 : ℝ)+(1399/12500 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (1409615859224488307/1410000000000000000 : ℝ)+(2508766787/1762500000000 : ℝ)*((14717/100000 : ℝ)+(1399/12500 : ℝ))=(10000963520099031/10000000000000000 : ℝ) by norm_num, show 1+(482914595549423/1562500000000000000 : ℝ)+(9738860986353613/100000000000000000000 : ℝ)=(20008129079020303337/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(482914595549423/1562500000000000000 : ℝ) ≤ ((1409615859224488307/1410000000000000000 : ℝ)+2*(2508766787/1762500000000 : ℝ)*(14717/100000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (1409615859224488307/1410000000000000000 : ℝ)+2*(2508766787/1762500000000 : ℝ)*(14717/100000 : ℝ)=(10001465273456431/10000000000000000 : ℝ) by norm_num, show 1+2*(482914595549423/1562500000000000000 : ℝ)=(781732914595549423/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1409615859224488307/1410000000000000000 : ℝ)*(X 1 0+X 2 0)+(2508766787/1762500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (1409615859224488307/1410000000000000000 : ℝ)) (alpha := (2508766787/1762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1409615859224488307/1410000000000000000 : ℝ)*(X 0 1+X 2 1)+(2508766787/1762500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (1409615859224488307/1410000000000000000 : ℝ)) (alpha := (2508766787/1762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1409615859224488307/1410000000000000000 : ℝ)*(X 0 2+X 1 2)+(2508766787/1762500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (1409615859224488307/1410000000000000000 : ℝ)) (alpha := (2508766787/1762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-232836831/1250000000 : ℝ)*X 0 0+(5389182601/10000000000 : ℝ)*X 0 1+(5389183159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((264270063/500000000 : ℝ)*X 1 0+(-2004967089/10000000000 : ℝ)*X 1 1+(1077836509/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057080217/2000000000 : ℝ)*X 2 0+(336823919/625000000 : ℝ)*X 2 1+(-2004967109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4469703293/10000000000 : ℝ)*X 0 0+(4251903793/10000000000 : ℝ)*X 0 1+(4251903991/10000000000 : ℝ)*X 0 2+(4469703293/10000000000 : ℝ)*X 1 0+(4251903793/10000000000 : ℝ)*X 1 1+(4251903991/10000000000 : ℝ)*X 1 2+(4469703293/10000000000 : ℝ)*X 2 0+(4251903793/10000000000 : ℝ)*X 2 1+(4251903991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219710359/1000000000 : ℝ)*X 0 0+(5265314101/10000000000 : ℝ)*X 0 1+(5265314581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372337489/10000000000 : ℝ)*X 1 0+(-1027398119/5000000000 : ℝ)*X 1 1+(5265314761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343084341/2500000000 : ℝ)*X 2 0+(263265743/500000000 : ℝ)*X 2 1+(-1027398137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173220319/10000000000 : ℝ)*X 0 0+(4400092281/10000000000 : ℝ)*X 0 1+(4400092503/10000000000 : ℝ)*X 0 2+(4173220319/10000000000 : ℝ)*X 1 0+(4400092281/10000000000 : ℝ)*X 1 1+(4400092503/10000000000 : ℝ)*X 1 2+(4173220319/10000000000 : ℝ)*X 2 0+(4400092281/10000000000 : ℝ)*X 2 1+(4400092503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2126831063/10000000000 : ℝ)*X 0 0+(2589977931/5000000000 : ℝ)*X 0 1+(84424903/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275562111/10000000000 : ℝ)*X 1 0+(-999599819/5000000000 : ℝ)*X 1 1+(1350798519/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637781209/5000000000 : ℝ)*X 2 0+(1350798481/2500000000 : ℝ)*X 2 1+(-1999199431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1125670063/2500000000 : ℝ)*X 0 0+(66173881/156250000 : ℝ)*X 0 1+(2117563871/5000000000 : ℝ)*X 0 2+(1125670063/2500000000 : ℝ)*X 1 0+(66173881/156250000 : ℝ)*X 1 1+(2117563871/5000000000 : ℝ)*X 1 2+(1125670063/2500000000 : ℝ)*X 2 0+(66173881/156250000 : ℝ)*X 2 1+(2117563871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-120829321/625000000 : ℝ)*X 0 0+(5472376653/10000000000 : ℝ)*X 0 1+(656778933/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380114149/10000000000 : ℝ)*X 1 0+(-1029575957/5000000000 : ℝ)*X 1 1+(5254231297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690057087/5000000000 : ℝ)*X 2 0+(5254231353/10000000000 : ℝ)*X 2 1+(-411830361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1036561127/2500000000 : ℝ)*X 0 0+(2206670679/5000000000 : ℝ)*X 0 1+(551667517/1250000000 : ℝ)*X 0 2+(1036561127/2500000000 : ℝ)*X 1 0+(2206670679/5000000000 : ℝ)*X 1 1+(551667517/1250000000 : ℝ)*X 1 2+(1036561127/2500000000 : ℝ)*X 2 0+(2206670679/5000000000 : ℝ)*X 2 1+(551667517/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62863/100000 : ℝ) ≤ (-923259479500667528771908365117/1468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2122113/20000000000000 : ℝ)*(upper1) + (59375513/100000000000000 : ℝ)*(lower4) + (8670387/20000000000000 : ℝ)*(upper5) + (183806410386027/6250000000000 : ℝ)*(major0) + (183806410386027/6250000000000 : ℝ)*(major1) + (183806410386027/6250000000000 : ℝ)*(major2) + (2355304927/100000000000000 : ℝ)*(sp3) + (4010743618504209/100000000000000 : ℝ)*(sp4) + (2005334454593093/50000000000000 : ℝ)*(sp5) + (4010680793699759/100000000000000 : ℝ)*(sp6) + (1892003789754047/100000000000000 : ℝ)*(sp7) + (8775416641/100000000000000 : ℝ)*(sp12) + (10435591833/12500000000000 : ℝ)*(sp13) + (17900055273/25000000000000 : ℝ)*(sp14) + (946003072529487/50000000000000 : ℝ)*(f.failure) + (80215047878417/2000000000000 : ℝ)*(f.sum) + (77010181053/117500000000000000000000000 : ℝ)*base66 + (28738013518128763/2937500000000000000000000000000 : ℝ)*base67 + (16214851324566263/2937500000000000000000000000000 : ℝ)*base69 + (20244054567003763/2937500000000000000000000000000 : ℝ)*base71 + (606956452783/117500000000000000000000000 : ℝ)*base74 + (18965212302878763/2937500000000000000000000000000 : ℝ)*base75 + (5995518722128763/2937500000000000000000000000000 : ℝ)*base77 + (11031402324503763/2937500000000000000000000000000 : ℝ)*base79 + (41496491669/14687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (121773/62500000000000000000 : ℝ)*base89 + (121773/62500000000000000000 : ℝ)*base91 + (121773/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1843/3125 : ℝ) ≤ (86625197515071131077782709029/146875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1886403/20000000000000 : ℝ)*(lower0) + (95338091/100000000000000 : ℝ)*(lower1) + (3148869/25000000000000 : ℝ)*(lower3) + (54987813/50000000000000 : ℝ)*(lower5) + (18813739851199/625000000000 : ℝ)*(major0) + (18813739851199/625000000000 : ℝ)*(major1) + (18813739851199/625000000000 : ℝ)*(major2) + (4064132965742421/100000000000000 : ℝ)*(sp0) + (2032038898765507/50000000000000 : ℝ)*(sp1) + (2032075041437209/50000000000000 : ℝ)*(sp2) + (484144618686919/25000000000000 : ℝ)*(sp3) + (8575467381/100000000000000 : ℝ)*(sp7) + (18071335851/25000000000000 : ℝ)*(sp9) + (17117131997/100000000000000 : ℝ)*(sp12) + (1936587050215057/100000000000000 : ℝ)*(f.failure) + (2032075041437209/50000000000000 : ℝ)*(f.sum) + (39631524259/141000000000000000000000000 : ℝ)*base66 + (568209252496219/293750000000000000000000000000 : ℝ)*base68 + (2299735346277469/293750000000000000000000000000 : ℝ)*base70 + (746941704371219/293750000000000000000000000000 : ℝ)*base72 + (97107484543/141000000000000000000000000 : ℝ)*base74 + (3944671833708719/293750000000000000000000000000 : ℝ)*base76 + (677939842883719/293750000000000000000000000000 : ℝ)*base78 + (299951820433719/293750000000000000000000000000 : ℝ)*base80 + (660482412649/141000000000000000000000000 : ℝ)*base82 + (1234803/125000000000000000000 : ℝ)*base89 + (1234803/125000000000000000000 : ℝ)*base91 + (1234803/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80059/100000 : ℝ) ≤ (9407247036076168273689111741867/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129246707/100000000000000 : ℝ)*(lower3) + (200345569/100000000000000 : ℝ)*(upper4) + (105267519/50000000000000 : ℝ)*(lower5) + (1660778556527081/50000000000000 : ℝ)*(major0) + (1660778556527081/50000000000000 : ℝ)*(major1) + (1660778556527081/50000000000000 : ℝ)*(major2) + (55022233/6250000000000 : ℝ)*(sp0) + (22989884887/12500000000000 : ℝ)*(sp1) + (247782271941/100000000000000 : ℝ)*(sp2) + (15012828879/10000000000000 : ℝ)*(sp3) + (2239764458371319/50000000000000 : ℝ)*(sp8) + (447934587801927/10000000000000 : ℝ)*(sp9) + (559910251853303/12500000000000 : ℝ)*(sp10) + (267093384385863/12500000000000 : ℝ)*(sp11) + (1068448601687847/50000000000000 : ℝ)*(f.failure) + (2239764898549183/50000000000000 : ℝ)*(f.sum) + (246998971187/176250000000000000000000000 : ℝ)*base66 + (210030396711352711/23500000000000000000000000000000 : ℝ)*base68 + (196909021687352711/23500000000000000000000000000000 : ℝ)*base70 + (166953700984352711/23500000000000000000000000000000 : ℝ)*base72 + (847439280229/352500000000000000000000000 : ℝ)*base74 + (82824412799352711/23500000000000000000000000000000 : ℝ)*base76 + (35234440771147289/23500000000000000000000000000000 : ℝ)*base77 + (150661145022647289/23500000000000000000000000000000 : ℝ)*base79 + (2527575593273/705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26213/62500000000000000000 : ℝ)*base89 + (26213/62500000000000000000 : ℝ)*base91 + (26213/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42211/50000 : ℝ) ≤ (-4959637736511658378225295859023/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166298211/100000000000000 : ℝ)*(lower0) + (111033927/100000000000000 : ℝ)*(lower2) + (94955177/100000000000000 : ℝ)*(upper3) + (764461/5000000000000 : ℝ)*(lower4) + (1679110346532811/50000000000000 : ℝ)*(major0) + (1679110346532811/50000000000000 : ℝ)*(major1) + (1679110346532811/50000000000000 : ℝ)*(major2) + (142094859/10000000000000 : ℝ)*(sp0) + (86022535297/50000000000000 : ℝ)*(sp5) + (15915633039/25000000000000 : ℝ)*(sp6) + (143252979044133/3125000000000 : ℝ)*(sp12) + (4583924705290253/100000000000000 : ℝ)*(sp13) + (458403308782869/10000000000000 : ℝ)*(sp14) + (108024221217317/5000000000000 : ℝ)*(sp15) + (108024221217317/5000000000000 : ℝ)*(f.failure) + (2292048375180423/50000000000000 : ℝ)*(f.sum) + (254458446587/44062500000000000000000000 : ℝ)*base65 + (60470222510686341/23500000000000000000000000000000 : ℝ)*base68 + (70118132376686341/23500000000000000000000000000000 : ℝ)*base70 + (1304689881528186341/23500000000000000000000000000000 : ℝ)*base72 + (2543977323691/352500000000000000000000000 : ℝ)*base73 + (152877320530186341/23500000000000000000000000000000 : ℝ)*base76 + (20845887531686341/23500000000000000000000000000000 : ℝ)*base78 + (178862849147313659/23500000000000000000000000000000 : ℝ)*base79 + (535681205159/352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7657/6250000000000000000 : ℝ)*base90 + (7657/6250000000000000000 : ℝ)*base92 + (7657/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1360_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1843/3125 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42211/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1360_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1360_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1843/3125 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42211/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1360_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1360_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1843/3125 : ℝ) else (80059/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42211/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
