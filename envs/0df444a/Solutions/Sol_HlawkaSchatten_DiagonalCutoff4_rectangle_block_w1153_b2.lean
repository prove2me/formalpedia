-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1153_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:54.513053+00:00
-- url     : https://prove2.me/submissions/cf69beea-f727-43c8-bedb-04bbea10c9b8

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
theorem support_rectangle_w1153_s6_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161609859/10000000000 : ℝ)*x 0 + (2696579871/5000000000 : ℝ)*x 1 + (1053121649/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161609859/10000000000 : ℝ)^4173 ≤ (13135858783481/100000000000000 : ℝ)^3149 := by
    have hnat : (2161609859 : ℕ)^4173*100000000000000^3149 ≤ 13135858783481^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161609859 10000000000 13135858783481 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696579871/5000000000 : ℝ)^4173 ≤ (1103020020423/2500000000000 : ℝ)^3149 := by
    have hnat : (2696579871 : ℕ)^4173*2500000000000^3149 ≤ 1103020020423^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696579871 5000000000 1103020020423 2500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053121649/2000000000 : ℝ)^4173 ≤ (10685835097693/25000000000000 : ℝ)^3149 := by
    have hnat : (1053121649 : ℕ)^4173*25000000000000^3149 ≤ 10685835097693^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053121649 2000000000 10685835097693 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161609859/10000000000 : ℝ), (2696579871/5000000000 : ℝ), (1053121649/2000000000 : ℝ)] ![(13135858783481/100000000000000 : ℝ), (1103020020423/2500000000000 : ℝ), (10685835097693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161609859/10000000000 : ℝ)|^4173 ≤ (13135858783481/100000000000000 : ℝ)^3149
        have hw : |(-2161609859/10000000000 : ℝ)|=(2161609859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696579871/5000000000 : ℝ)|^4173 ≤ (1103020020423/2500000000000 : ℝ)^3149
        have hw : |(2696579871/5000000000 : ℝ)|=(2696579871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053121649/2000000000 : ℝ)|^4173 ≤ (10685835097693/25000000000000 : ℝ)^3149
        have hw : |(1053121649/2000000000 : ℝ)|=(1053121649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336199369/2500000000 : ℝ)*x 0 + (-445261701/2000000000 : ℝ)*x 1 + (1316402091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336199369/2500000000 : ℝ)^4173 ≤ (21798631826469/50000000000000 : ℝ)^3149 := by
    have hnat : (1336199369 : ℕ)^4173*50000000000000^3149 ≤ 21798631826469^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336199369 2500000000 21798631826469 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445261701/2000000000 : ℝ)^4173 ≤ (13659394661263/100000000000000 : ℝ)^3149 := by
    have hnat : (445261701 : ℕ)^4173*100000000000000^3149 ≤ 13659394661263^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445261701 2000000000 13659394661263 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316402091/2500000000 : ℝ)^4173 ≤ (10685835417717/25000000000000 : ℝ)^3149 := by
    have hnat : (1316402091 : ℕ)^4173*25000000000000^3149 ≤ 10685835417717^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316402091 2500000000 10685835417717 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336199369/2500000000 : ℝ), (-445261701/2000000000 : ℝ), (1316402091/2500000000 : ℝ)] ![(21798631826469/50000000000000 : ℝ), (13659394661263/100000000000000 : ℝ), (10685835417717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336199369/2500000000 : ℝ)|^4173 ≤ (21798631826469/50000000000000 : ℝ)^3149
        have hw : |(1336199369/2500000000 : ℝ)|=(1336199369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445261701/2000000000 : ℝ)|^4173 ≤ (13659394661263/100000000000000 : ℝ)^3149
        have hw : |(-445261701/2000000000 : ℝ)|=(445261701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316402091/2500000000 : ℝ)|^4173 ≤ (10685835417717/25000000000000 : ℝ)^3149
        have hw : |(1316402091/2500000000 : ℝ)|=(1316402091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344797997/10000000000 : ℝ)*x 0 + (526560793/1000000000 : ℝ)*x 1 + (-1113154193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344797997/10000000000 : ℝ)^4173 ≤ (21798634642331/50000000000000 : ℝ)^3149 := by
    have hnat : (5344797997 : ℕ)^4173*50000000000000^3149 ≤ 21798634642331^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344797997 10000000000 21798634642331 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526560793/1000000000 : ℝ)^4173 ≤ (21371668501141/50000000000000 : ℝ)^3149 := by
    have hnat : (526560793 : ℕ)^4173*50000000000000^3149 ≤ 21371668501141^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526560793 1000000000 21371668501141 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113154193/5000000000 : ℝ)^4173 ≤ (13659393693723/100000000000000 : ℝ)^3149 := by
    have hnat : (1113154193 : ℕ)^4173*100000000000000^3149 ≤ 13659393693723^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113154193 5000000000 13659393693723 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344797997/10000000000 : ℝ), (526560793/1000000000 : ℝ), (-1113154193/5000000000 : ℝ)] ![(21798634642331/50000000000000 : ℝ), (21371668501141/50000000000000 : ℝ), (13659393693723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344797997/10000000000 : ℝ)|^4173 ≤ (21798634642331/50000000000000 : ℝ)^3149
        have hw : |(5344797997/10000000000 : ℝ)|=(5344797997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526560793/1000000000 : ℝ)|^4173 ≤ (21371668501141/50000000000000 : ℝ)^3149
        have hw : |(526560793/1000000000 : ℝ)|=(526560793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113154193/5000000000 : ℝ)|^4173 ≤ (13659393693723/100000000000000 : ℝ)^3149
        have hw : |(-1113154193/5000000000 : ℝ)|=(1113154193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (109077757/250000000 : ℝ)*x 0 + (264862117/625000000 : ℝ)*x 1 + (4492102841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109077757/250000000 : ℝ)^4173 ≤ (16658434437673/50000000000000 : ℝ)^3149 := by
    have hnat : (109077757 : ℕ)^4173*50000000000000^3149 ≤ 16658434437673^3149*250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109077757 250000000 16658434437673 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264862117/625000000 : ℝ)^4173 ≤ (32054734901771/100000000000000 : ℝ)^3149 := by
    have hnat : (264862117 : ℕ)^4173*100000000000000^3149 ≤ 32054734901771^3149*625000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264862117 625000000 32054734901771 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492102841/10000000000 : ℝ)^4173 ≤ (4328549524667/12500000000000 : ℝ)^3149 := by
    have hnat : (4492102841 : ℕ)^4173*12500000000000^3149 ≤ 4328549524667^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492102841 10000000000 4328549524667 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109077757/250000000 : ℝ), (264862117/625000000 : ℝ), (4492102841/10000000000 : ℝ)] ![(16658434437673/50000000000000 : ℝ), (32054734901771/100000000000000 : ℝ), (4328549524667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109077757/250000000 : ℝ)|^4173 ≤ (16658434437673/50000000000000 : ℝ)^3149
        have hw : |(109077757/250000000 : ℝ)|=(109077757/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264862117/625000000 : ℝ)|^4173 ≤ (32054734901771/100000000000000 : ℝ)^3149
        have hw : |(264862117/625000000 : ℝ)|=(264862117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492102841/10000000000 : ℝ)|^4173 ≤ (4328549524667/12500000000000 : ℝ)^3149
        have hw : |(4492102841/10000000000 : ℝ)|=(4492102841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080807509/5000000000 : ℝ)*x 0 + (5265930187/10000000000 : ℝ)*x 1 + (5392836457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080807509/5000000000 : ℝ)^4173 ≤ (6567950164423/50000000000000 : ℝ)^3149 := by
    have hnat : (1080807509 : ℕ)^4173*50000000000000^3149 ≤ 6567950164423^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080807509 5000000000 6567950164423 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265930187/10000000000 : ℝ)^4173 ≤ (8549360718187/20000000000000 : ℝ)^3149 := by
    have hnat : (5265930187 : ℕ)^4173*20000000000000^3149 ≤ 8549360718187^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265930187 10000000000 8549360718187 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392836457/10000000000 : ℝ)^4173 ≤ (44117296066083/100000000000000 : ℝ)^3149 := by
    have hnat : (5392836457 : ℕ)^4173*100000000000000^3149 ≤ 44117296066083^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392836457 10000000000 44117296066083 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080807509/5000000000 : ℝ), (5265930187/10000000000 : ℝ), (5392836457/10000000000 : ℝ)] ![(6567950164423/50000000000000 : ℝ), (8549360718187/20000000000000 : ℝ), (44117296066083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080807509/5000000000 : ℝ)|^4173 ≤ (6567950164423/50000000000000 : ℝ)^3149
        have hw : |(-1080807509/5000000000 : ℝ)|=(1080807509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265930187/10000000000 : ℝ)|^4173 ≤ (8549360718187/20000000000000 : ℝ)^3149
        have hw : |(5265930187/10000000000 : ℝ)|=(5265930187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392836457/10000000000 : ℝ)|^4173 ≤ (44117296066083/100000000000000 : ℝ)^3149
        have hw : |(5392836457/10000000000 : ℝ)|=(5392836457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328113987/2500000000 : ℝ)*x 0 + (-131192493/625000000 : ℝ)*x 1 + (1348209119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328113987/2500000000 : ℝ)^4173 ≤ (10812003463509/25000000000000 : ℝ)^3149 := by
    have hnat : (1328113987 : ℕ)^4173*25000000000000^3149 ≤ 10812003463509^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328113987 2500000000 10812003463509 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131192493/625000000 : ℝ)^4173 ≤ (12634689864923/100000000000000 : ℝ)^3149 := by
    have hnat : (131192493 : ℕ)^4173*100000000000000^3149 ≤ 12634689864923^3149*625000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131192493 625000000 12634689864923 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348209119/2500000000 : ℝ)^4173 ≤ (44117296272061/100000000000000 : ℝ)^3149 := by
    have hnat : (1348209119 : ℕ)^4173*100000000000000^3149 ≤ 44117296272061^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348209119 2500000000 44117296272061 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328113987/2500000000 : ℝ), (-131192493/625000000 : ℝ), (1348209119/2500000000 : ℝ)] ![(10812003463509/25000000000000 : ℝ), (12634689864923/100000000000000 : ℝ), (44117296272061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328113987/2500000000 : ℝ)|^4173 ≤ (10812003463509/25000000000000 : ℝ)^3149
        have hw : |(1328113987/2500000000 : ℝ)|=(1328113987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131192493/625000000 : ℝ)|^4173 ≤ (12634689864923/100000000000000 : ℝ)^3149
        have hw : |(-131192493/625000000 : ℝ)|=(131192493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348209119/2500000000 : ℝ)|^4173 ≤ (44117296272061/100000000000000 : ℝ)^3149
        have hw : |(1348209119/2500000000 : ℝ)|=(1348209119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312455949/10000000000 : ℝ)*x 0 + (1348209119/2500000000 : ℝ)*x 1 + (-419815977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312455949/10000000000 : ℝ)^4173 ≤ (5406001733103/12500000000000 : ℝ)^3149 := by
    have hnat : (5312455949 : ℕ)^4173*12500000000000^3149 ≤ 5406001733103^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312455949 10000000000 5406001733103 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348209119/2500000000 : ℝ)^4173 ≤ (44117296272061/100000000000000 : ℝ)^3149 := by
    have hnat : (1348209119 : ℕ)^4173*100000000000000^3149 ≤ 44117296272061^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348209119 2500000000 44117296272061 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419815977/2000000000 : ℝ)^4173 ≤ (12634689840993/100000000000000 : ℝ)^3149 := by
    have hnat : (419815977 : ℕ)^4173*100000000000000^3149 ≤ 12634689840993^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419815977 2000000000 12634689840993 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312455949/10000000000 : ℝ), (1348209119/2500000000 : ℝ), (-419815977/2000000000 : ℝ)] ![(5406001733103/12500000000000 : ℝ), (44117296272061/100000000000000 : ℝ), (12634689840993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312455949/10000000000 : ℝ)|^4173 ≤ (5406001733103/12500000000000 : ℝ)^3149
        have hw : |(5312455949/10000000000 : ℝ)|=(5312455949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348209119/2500000000 : ℝ)|^4173 ≤ (44117296272061/100000000000000 : ℝ)^3149
        have hw : |(1348209119/2500000000 : ℝ)|=(1348209119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419815977/2000000000 : ℝ)|^4173 ≤ (12634689840993/100000000000000 : ℝ)^3149
        have hw : |(-419815977/2000000000 : ℝ)|=(419815977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s6_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363119507/10000000000 : ℝ)*x 0 + (4491460649/10000000000 : ℝ)*x 1 + (2119219503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363119507/10000000000 : ℝ)^4173 ≤ (16658481122353/50000000000000 : ℝ)^3149 := by
    have hnat : (4363119507 : ℕ)^4173*50000000000000^3149 ≤ 16658481122353^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363119507 10000000000 16658481122353 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491460649/10000000000 : ℝ)^4173 ≤ (3462183605583/10000000000000 : ℝ)^3149 := by
    have hnat : (4491460649 : ℕ)^4173*10000000000000^3149 ≤ 3462183605583^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491460649 10000000000 3462183605583 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119219503/5000000000 : ℝ)^4173 ≤ (1001912552871/3125000000000 : ℝ)^3149 := by
    have hnat : (2119219503 : ℕ)^4173*3125000000000^3149 ≤ 1001912552871^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119219503 5000000000 1001912552871 3125000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363119507/10000000000 : ℝ), (4491460649/10000000000 : ℝ), (2119219503/5000000000 : ℝ)] ![(16658481122353/50000000000000 : ℝ), (3462183605583/10000000000000 : ℝ), (1001912552871/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363119507/10000000000 : ℝ)|^4173 ≤ (16658481122353/50000000000000 : ℝ)^3149
        have hw : |(4363119507/10000000000 : ℝ)|=(4363119507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491460649/10000000000 : ℝ)|^4173 ≤ (3462183605583/10000000000000 : ℝ)^3149
        have hw : |(4491460649/10000000000 : ℝ)|=(4491460649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119219503/5000000000 : ℝ)|^4173 ≤ (1001912552871/3125000000000 : ℝ)^3149
        have hw : |(2119219503/5000000000 : ℝ)|=(2119219503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11331/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (109448591343373/781250000000000000 : ℝ) := by
    have hpowers : (11331/100000 : ℝ)^8345 ≤ (109448591343373/781250000000000000 : ℝ)^2048 := by
      have hnat : (11331 : ℕ)^8345*781250000000000000^2048 ≤ 109448591343373^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11331 100000 109448591343373 781250000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11331/100000 : ℝ)) (X := (109448591343373/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (34075197524869917/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^8345 ≤ (34075197524869917/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14093 : ℕ)^8345*100000000000000000000^2048 ≤ 34075197524869917^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 34075197524869917 100000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (34075197524869917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (390734448591343373/390625000000000000 : ℝ) ≤ (10000687555637863/10000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (390734448591343373/390625000000000000 : ℝ)^2048 ≤ (10000687555637863/10000000000000000 : ℝ)^8345 := by
      have hnat : (390734448591343373 : ℕ)^2048*10000000000000000^8345 ≤ 10000687555637863^8345*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390734448591343373 390625000000000000 10000687555637863 10000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000687555637863/10000000000000000 : ℝ)) (X := (390734448591343373/390625000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048084617216821661/100000000000000000000 : ℝ) ≤ (2000235972283761/2000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (100048084617216821661/100000000000000000000 : ℝ)^2048 ≤ (2000235972283761/2000000000000000 : ℝ)^8345 := by
      have hnat : (100048084617216821661 : ℕ)^2048*2000000000000000^8345 ≤ 2000235972283761^8345*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048084617216821661 100000000000000000000 2000235972283761 2000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000235972283761/2000000000000000 : ℝ)) (X := (100048084617216821661/100000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034075197524869917/50000000000000000000 : ℝ) ≤ (10001672167199747/10000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (50034075197524869917/50000000000000000000 : ℝ)^2048 ≤ (10001672167199747/10000000000000000 : ℝ)^8345 := by
      have hnat : (50034075197524869917 : ℕ)^2048*10000000000000000^8345 ≤ 10001672167199747^8345*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034075197524869917 50000000000000000000 10001672167199747 10000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672167199747/10000000000000000 : ℝ)) (X := (50034075197524869917/50000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109448591343373/781250000000000000 : ℝ) ≤ ((13805371197532035001/13810000000000000000 : ℝ)+2*(246152890471/138100000000000 : ℝ)*(11331/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (13805371197532035001/13810000000000000000 : ℝ)+2*(246152890471/138100000000000 : ℝ)*(11331/100000 : ℝ)=(10000687555637863/10000000000000000 : ℝ) by norm_num, show 1+2*(109448591343373/781250000000000000 : ℝ)=(390734448591343373/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34075197524869917/100000000000000000000 : ℝ)+(109448591343373/781250000000000000 : ℝ) ≤ ((13805371197532035001/13810000000000000000 : ℝ)+(246152890471/138100000000000 : ℝ)*((14093/100000 : ℝ)+(11331/100000 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (13805371197532035001/13810000000000000000 : ℝ)+(246152890471/138100000000000 : ℝ)*((14093/100000 : ℝ)+(11331/100000 : ℝ))=(2000235972283761/2000000000000000 : ℝ) by norm_num, show 1+(34075197524869917/100000000000000000000 : ℝ)+(109448591343373/781250000000000000 : ℝ)=(100048084617216821661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34075197524869917/100000000000000000000 : ℝ) ≤ ((13805371197532035001/13810000000000000000 : ℝ)+2*(246152890471/138100000000000 : ℝ)*(14093/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (13805371197532035001/13810000000000000000 : ℝ)+2*(246152890471/138100000000000 : ℝ)*(14093/100000 : ℝ)=(10001672167199747/10000000000000000 : ℝ) by norm_num, show 1+2*(34075197524869917/100000000000000000000 : ℝ)=(50034075197524869917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13805371197532035001/13810000000000000000 : ℝ)*(X 1 0+X 2 0)+(246152890471/138100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13805371197532035001/13810000000000000000 : ℝ)) (alpha := (246152890471/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13805371197532035001/13810000000000000000 : ℝ)*(X 0 1+X 2 1)+(246152890471/138100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13805371197532035001/13810000000000000000 : ℝ)) (alpha := (246152890471/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13805371197532035001/13810000000000000000 : ℝ)*(X 0 2+X 1 2)+(246152890471/138100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (13805371197532035001/13810000000000000000 : ℝ)) (alpha := (246152890471/138100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161609859/10000000000 : ℝ)*X 0 0+(2696579871/5000000000 : ℝ)*X 0 1+(1053121649/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336199369/2500000000 : ℝ)*X 1 0+(-445261701/2000000000 : ℝ)*X 1 1+(1316402091/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344797997/10000000000 : ℝ)*X 2 0+(526560793/1000000000 : ℝ)*X 2 1+(-1113154193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109077757/250000000 : ℝ)*X 0 0+(264862117/625000000 : ℝ)*X 0 1+(4492102841/10000000000 : ℝ)*X 0 2+(109077757/250000000 : ℝ)*X 1 0+(264862117/625000000 : ℝ)*X 1 1+(4492102841/10000000000 : ℝ)*X 1 2+(109077757/250000000 : ℝ)*X 2 0+(264862117/625000000 : ℝ)*X 2 1+(4492102841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080807509/5000000000 : ℝ)*X 0 0+(5265930187/10000000000 : ℝ)*X 0 1+(5392836457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328113987/2500000000 : ℝ)*X 1 0+(-131192493/625000000 : ℝ)*X 1 1+(1348209119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312455949/10000000000 : ℝ)*X 2 0+(1348209119/2500000000 : ℝ)*X 2 1+(-419815977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363119507/10000000000 : ℝ)*X 0 0+(4491460649/10000000000 : ℝ)*X 0 1+(2119219503/5000000000 : ℝ)*X 0 2+(4363119507/10000000000 : ℝ)*X 1 0+(4491460649/10000000000 : ℝ)*X 1 1+(2119219503/5000000000 : ℝ)*X 1 2+(4363119507/10000000000 : ℝ)*X 2 0+(4491460649/10000000000 : ℝ)*X 2 1+(2119219503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1756840765071352373875428039/345250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130330079/50000000000000 : ℝ)*(base19) + (9221611/2500000000000 : ℝ)*(base23) + (399768923/100000000000000 : ℝ)*(lower2) + (866809/400000000000 : ℝ)*(upper3) + (49140021/100000000000000 : ℝ)*(lower4) + (15787769/25000000000000 : ℝ)*(upper5) + (5886097063478987/100000000000000 : ℝ)*(major0) + (5886097063478987/100000000000000 : ℝ)*(major1) + (5886097063478987/100000000000000 : ℝ)*(major2) + (783996008491163/10000000000000 : ℝ)*(sp0) + (7839959824251471/100000000000000 : ℝ)*(sp1) + (783995971604719/10000000000000 : ℝ)*(sp2) + (1966111957874973/50000000000000 : ℝ)*(sp3) + (398267049/4000000000000 : ℝ)*(sp7) + (983058468106543/25000000000000 : ℝ)*(f.failure) + (783996008491163/10000000000000 : ℝ)*(f.sum) + (36788329146863/1726250000000000000000000000 : ℝ)*base65 + (18323106733942723987/1381000000000000000000000000000000 : ℝ)*base67 + (5199024729233723987/1381000000000000000000000000000000 : ℝ)*base69 + (37466041580668723987/1381000000000000000000000000000000 : ℝ)*base71 + (3615392266667/6905000000000000000000000000 : ℝ)*base73 + (17880957234580276013/1381000000000000000000000000000000 : ℝ)*base76 + (4212402286514723987/1381000000000000000000000000000000 : ℝ)*base77 + (63378760325502723987/1381000000000000000000000000000000 : ℝ)*base79 + (61356013752497/6905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9750711/2500000000000000000000 : ℝ)*base89 + (9750711/2500000000000000000000 : ℝ)*base91 + (9750711/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (740481706522161545435787387/69050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1963989979/100000000000000 : ℝ)*(base19) + (266338953/12500000000000 : ℝ)*(base23) + (226257969/100000000000000 : ℝ)*(upper3) + (73119633/100000000000000 : ℝ)*(lower4) + (215253981/100000000000000 : ℝ)*(upper5) + (591603000035871/10000000000000 : ℝ)*(major0) + (591603000035871/10000000000000 : ℝ)*(major1) + (591603000035871/10000000000000 : ℝ)*(major2) + (54512795551/100000000000000 : ℝ)*(sp1) + (14761374611/25000000000000 : ℝ)*(sp2) + (3939914468209813/50000000000000 : ℝ)*(sp4) + (7879772459634097/100000000000000 : ℝ)*(sp5) + (3939883880104779/50000000000000 : ℝ)*(sp6) + (1976115353418091/50000000000000 : ℝ)*(sp7) + (1976115353418091/50000000000000 : ℝ)*(f.failure) + (3939914468209813/50000000000000 : ℝ)*(f.sum) + (2822870170799/345250000000000000000000000 : ℝ)*base65 + (227174252906379129/138100000000000000000000000000000 : ℝ)*base68 + (293508597122220871/138100000000000000000000000000000 : ℝ)*base69 + (207058375726979129/138100000000000000000000000000000 : ℝ)*base72 + (1665255869499/276200000000000000000000000 : ℝ)*base73 + (274256676304820871/138100000000000000000000000000000 : ℝ)*base75 + (63411996411220871/138100000000000000000000000000000 : ℝ)*base77 + (2388073993939020871/138100000000000000000000000000000 : ℝ)*base79 + (1647237343991/345250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (55771693/5000000000000000000000 : ℝ)*base90 + (55771693/5000000000000000000000 : ℝ)*base92 + (55771693/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1153_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1153_s7_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080816021/5000000000 : ℝ)*x 0 + (16852683/31250000 : ℝ)*x 1 + (20569903/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080816021/5000000000 : ℝ)^4173 ≤ (6568018711571/50000000000000 : ℝ)^3149 := by
    have hnat : (1080816021 : ℕ)^4173*50000000000000^3149 ≤ 6568018711571^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080816021 5000000000 6568018711571 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16852683/31250000 : ℝ)^4173 ≤ (44117535683771/100000000000000 : ℝ)^3149 := by
    have hnat : (16852683 : ℕ)^4173*100000000000000^3149 ≤ 44117535683771^3149*31250000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16852683 31250000 44117535683771 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20569903/39062500 : ℝ)^4173 ≤ (42746426880593/100000000000000 : ℝ)^3149 := by
    have hnat : (20569903 : ℕ)^4173*100000000000000^3149 ≤ 42746426880593^3149*39062500^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20569903 39062500 42746426880593 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080816021/5000000000 : ℝ), (16852683/31250000 : ℝ), (20569903/39062500 : ℝ)] ![(6568018711571/50000000000000 : ℝ), (44117535683771/100000000000000 : ℝ), (42746426880593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080816021/5000000000 : ℝ)|^4173 ≤ (6568018711571/50000000000000 : ℝ)^3149
        have hw : |(-1080816021/5000000000 : ℝ)|=(1080816021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16852683/31250000 : ℝ)|^4173 ≤ (44117535683771/100000000000000 : ℝ)^3149
        have hw : |(16852683/31250000 : ℝ)|=(16852683/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20569903/39062500 : ℝ)|^4173 ≤ (42746426880593/100000000000000 : ℝ)^3149
        have hw : |(20569903/39062500 : ℝ)|=(20569903/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344723191/10000000000 : ℝ)*x 0 + (-2226027461/10000000000 : ℝ)*x 1 + (2632947713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344723191/10000000000 : ℝ)^4173 ≤ (10899115168641/25000000000000 : ℝ)^3149 := by
    have hnat : (5344723191 : ℕ)^4173*25000000000000^3149 ≤ 10899115168641^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344723191 10000000000 10899115168641 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226027461/10000000000 : ℝ)^4173 ≤ (13657109655837/100000000000000 : ℝ)^3149 := by
    have hnat : (2226027461 : ℕ)^4173*100000000000000^3149 ≤ 13657109655837^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226027461 10000000000 13657109655837 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632947713/5000000000 : ℝ)^4173 ≤ (42746429655977/100000000000000 : ℝ)^3149 := by
    have hnat : (2632947713 : ℕ)^4173*100000000000000^3149 ≤ 42746429655977^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632947713 5000000000 42746429655977 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344723191/10000000000 : ℝ), (-2226027461/10000000000 : ℝ), (2632947713/5000000000 : ℝ)] ![(10899115168641/25000000000000 : ℝ), (13657109655837/100000000000000 : ℝ), (42746429655977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344723191/10000000000 : ℝ)|^4173 ≤ (10899115168641/25000000000000 : ℝ)^3149
        have hw : |(5344723191/10000000000 : ℝ)|=(5344723191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226027461/10000000000 : ℝ)|^4173 ≤ (13657109655837/100000000000000 : ℝ)^3149
        have hw : |(-2226027461/10000000000 : ℝ)|=(2226027461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632947713/5000000000 : ℝ)|^4173 ≤ (42746429655977/100000000000000 : ℝ)^3149
        have hw : |(2632947713/5000000000 : ℝ)|=(2632947713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668090457/1250000000 : ℝ)*x 0 + (5265895001/10000000000 : ℝ)*x 1 + (-445205481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668090457/1250000000 : ℝ)^4173 ≤ (43596465700937/100000000000000 : ℝ)^3149 := by
    have hnat : (668090457 : ℕ)^4173*100000000000000^3149 ≤ 43596465700937^3149*1250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668090457 1250000000 43596465700937 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265895001/10000000000 : ℝ)^4173 ≤ (42746425084123/100000000000000 : ℝ)^3149 := by
    have hnat : (5265895001 : ℕ)^4173*100000000000000^3149 ≤ 42746425084123^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265895001 10000000000 42746425084123 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445205481/2000000000 : ℝ)^4173 ≤ (13657109200543/100000000000000 : ℝ)^3149 := by
    have hnat : (445205481 : ℕ)^4173*100000000000000^3149 ≤ 13657109200543^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445205481 2000000000 13657109200543 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668090457/1250000000 : ℝ), (5265895001/10000000000 : ℝ), (-445205481/2000000000 : ℝ)] ![(43596465700937/100000000000000 : ℝ), (42746425084123/100000000000000 : ℝ), (13657109200543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668090457/1250000000 : ℝ)|^4173 ≤ (43596465700937/100000000000000 : ℝ)^3149
        have hw : |(668090457/1250000000 : ℝ)|=(668090457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265895001/10000000000 : ℝ)|^4173 ≤ (42746425084123/100000000000000 : ℝ)^3149
        have hw : |(5265895001/10000000000 : ℝ)|=(5265895001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445205481/2000000000 : ℝ)|^4173 ≤ (13657109200543/100000000000000 : ℝ)^3149
        have hw : |(-445205481/2000000000 : ℝ)|=(445205481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218156231/500000000 : ℝ)*x 0 + (423837927/1000000000 : ℝ)*x 1 + (4491514203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218156231/500000000 : ℝ)^4173 ≤ (33317013983927/100000000000000 : ℝ)^3149 := by
    have hnat : (218156231 : ℕ)^4173*100000000000000^3149 ≤ 33317013983927^3149*500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218156231 500000000 33317013983927 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423837927/1000000000 : ℝ)^4173 ≤ (32060602887827/100000000000000 : ℝ)^3149 := by
    have hnat : (423837927 : ℕ)^4173*100000000000000^3149 ≤ 32060602887827^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423837927 1000000000 32060602887827 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491514203/10000000000 : ℝ)^4173 ≤ (34622383110811/100000000000000 : ℝ)^3149 := by
    have hnat : (4491514203 : ℕ)^4173*100000000000000^3149 ≤ 34622383110811^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491514203 10000000000 34622383110811 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218156231/500000000 : ℝ), (423837927/1000000000 : ℝ), (4491514203/10000000000 : ℝ)] ![(33317013983927/100000000000000 : ℝ), (32060602887827/100000000000000 : ℝ), (34622383110811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218156231/500000000 : ℝ)|^4173 ≤ (33317013983927/100000000000000 : ℝ)^3149
        have hw : |(218156231/500000000 : ℝ)|=(218156231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423837927/1000000000 : ℝ)|^4173 ≤ (32060602887827/100000000000000 : ℝ)^3149
        have hw : |(423837927/1000000000 : ℝ)|=(423837927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491514203/10000000000 : ℝ)|^4173 ≤ (34622383110811/100000000000000 : ℝ)^3149
        have hw : |(4491514203/10000000000 : ℝ)|=(4491514203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86465469/400000000 : ℝ)*x 0 + (131655363/250000000 : ℝ)*x 1 + (1348134547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86465469/400000000 : ℝ)^4173 ≤ (1313607513541/10000000000000 : ℝ)^3149 := by
    have hnat : (86465469 : ℕ)^4173*10000000000000^3149 ≤ 1313607513541^3149*400000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86465469 400000000 1313607513541 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131655363/250000000 : ℝ)^4173 ≤ (10687465570039/25000000000000 : ℝ)^3149 := by
    have hnat : (131655363 : ℕ)^4173*25000000000000^3149 ≤ 10687465570039^3149*250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131655363 250000000 10687465570039 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348134547/2500000000 : ℝ)^4173 ≤ (44114062575701/100000000000000 : ℝ)^3149 := by
    have hnat : (1348134547 : ℕ)^4173*100000000000000^3149 ≤ 44114062575701^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348134547 2500000000 44114062575701 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86465469/400000000 : ℝ), (131655363/250000000 : ℝ), (1348134547/2500000000 : ℝ)] ![(1313607513541/10000000000000 : ℝ), (10687465570039/25000000000000 : ℝ), (44114062575701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86465469/400000000 : ℝ)|^4173 ≤ (1313607513541/10000000000000 : ℝ)^3149
        have hw : |(-86465469/400000000 : ℝ)|=(86465469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131655363/250000000 : ℝ)|^4173 ≤ (10687465570039/25000000000000 : ℝ)^3149
        have hw : |(131655363/250000000 : ℝ)|=(131655363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348134547/2500000000 : ℝ)|^4173 ≤ (44114062575701/100000000000000 : ℝ)^3149
        have hw : |(1348134547/2500000000 : ℝ)|=(1348134547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312530473/10000000000 : ℝ)*x 0 + (-2099384489/10000000000 : ℝ)*x 1 + (1348134547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312530473/10000000000 : ℝ)^4173 ≤ (43248817841959/100000000000000 : ℝ)^3149 := by
    have hnat : (5312530473 : ℕ)^4173*100000000000000^3149 ≤ 43248817841959^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312530473 10000000000 43248817841959 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099384489/10000000000 : ℝ)^4173 ≤ (12637119566377/100000000000000 : ℝ)^3149 := by
    have hnat : (2099384489 : ℕ)^4173*100000000000000^3149 ≤ 12637119566377^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099384489 10000000000 12637119566377 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348134547/2500000000 : ℝ)^4173 ≤ (44114062575701/100000000000000 : ℝ)^3149 := by
    have hnat : (1348134547 : ℕ)^4173*100000000000000^3149 ≤ 44114062575701^3149*2500000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348134547 2500000000 44114062575701 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312530473/10000000000 : ℝ), (-2099384489/10000000000 : ℝ), (1348134547/2500000000 : ℝ)] ![(43248817841959/100000000000000 : ℝ), (12637119566377/100000000000000 : ℝ), (44114062575701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312530473/10000000000 : ℝ)|^4173 ≤ (43248817841959/100000000000000 : ℝ)^3149
        have hw : |(5312530473/10000000000 : ℝ)|=(5312530473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099384489/10000000000 : ℝ)|^4173 ≤ (12637119566377/100000000000000 : ℝ)^3149
        have hw : |(-2099384489/10000000000 : ℝ)|=(2099384489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348134547/2500000000 : ℝ)|^4173 ≤ (44114062575701/100000000000000 : ℝ)^3149
        have hw : |(1348134547/2500000000 : ℝ)|=(1348134547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664066309/1250000000 : ℝ)*x 0 + (5392538189/10000000000 : ℝ)*x 1 + (-2099384489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664066309/1250000000 : ℝ)^4173 ≤ (4324881783117/10000000000000 : ℝ)^3149 := by
    have hnat : (664066309 : ℕ)^4173*10000000000000^3149 ≤ 4324881783117^3149*1250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664066309 1250000000 4324881783117 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392538189/10000000000 : ℝ)^4173 ≤ (22057031293271/50000000000000 : ℝ)^3149 := by
    have hnat : (5392538189 : ℕ)^4173*50000000000000^3149 ≤ 22057031293271^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392538189 10000000000 22057031293271 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099384489/10000000000 : ℝ)^4173 ≤ (12637119566377/100000000000000 : ℝ)^3149 := by
    have hnat : (2099384489 : ℕ)^4173*100000000000000^3149 ≤ 12637119566377^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099384489 10000000000 12637119566377 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664066309/1250000000 : ℝ), (5392538189/10000000000 : ℝ), (-2099384489/10000000000 : ℝ)] ![(4324881783117/10000000000000 : ℝ), (22057031293271/50000000000000 : ℝ), (12637119566377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664066309/1250000000 : ℝ)|^4173 ≤ (4324881783117/10000000000000 : ℝ)^3149
        have hw : |(664066309/1250000000 : ℝ)|=(664066309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392538189/10000000000 : ℝ)|^4173 ≤ (22057031293271/50000000000000 : ℝ)^3149
        have hw : |(5392538189/10000000000 : ℝ)|=(5392538189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099384489/10000000000 : ℝ)|^4173 ≤ (12637119566377/100000000000000 : ℝ)^3149
        have hw : |(-2099384489/10000000000 : ℝ)|=(2099384489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s7_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363134343/10000000000 : ℝ)*x 0 + (4490877887/10000000000 : ℝ)*x 1 + (4239017857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363134343/10000000000 : ℝ)^4173 ≤ (33317112372491/100000000000000 : ℝ)^3149 := by
    have hnat : (4363134343 : ℕ)^4173*100000000000000^3149 ≤ 33317112372491^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363134343 10000000000 33317112372491 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490877887/10000000000 : ℝ)^4173 ≤ (34615883269649/100000000000000 : ℝ)^3149 := by
    have hnat : (4490877887 : ℕ)^4173*100000000000000^3149 ≤ 34615883269649^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490877887 10000000000 34615883269649 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239017857/10000000000 : ℝ)^4173 ≤ (32067004337033/100000000000000 : ℝ)^3149 := by
    have hnat : (4239017857 : ℕ)^4173*100000000000000^3149 ≤ 32067004337033^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239017857 10000000000 32067004337033 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363134343/10000000000 : ℝ), (4490877887/10000000000 : ℝ), (4239017857/10000000000 : ℝ)] ![(33317112372491/100000000000000 : ℝ), (34615883269649/100000000000000 : ℝ), (32067004337033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363134343/10000000000 : ℝ)|^4173 ≤ (33317112372491/100000000000000 : ℝ)^3149
        have hw : |(4363134343/10000000000 : ℝ)|=(4363134343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490877887/10000000000 : ℝ)|^4173 ≤ (34615883269649/100000000000000 : ℝ)^3149
        have hw : |(4490877887/10000000000 : ℝ)|=(4490877887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239017857/10000000000 : ℝ)|^4173 ≤ (32067004337033/100000000000000 : ℝ)^3149
        have hw : |(4239017857/10000000000 : ℝ)|=(4239017857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (7080586278315919/50000000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^8345 ≤ (7080586278315919/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11361 : ℕ)^8345*50000000000000000000^2048 ≤ 7080586278315919^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 7080586278315919 50000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (7080586278315919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14063/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (8445149664309581/25000000000000000000 : ℝ) := by
    have hpowers : (14063/100000 : ℝ)^8345 ≤ (8445149664309581/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14063 : ℕ)^8345*25000000000000000000^2048 ≤ 8445149664309581^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14063 100000 8445149664309581 25000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14063/100000 : ℝ)) (X := (8445149664309581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007080586278315919/25000000000000000000 : ℝ) ≤ (500034750129189/500000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (25007080586278315919/25000000000000000000 : ℝ)^2048 ≤ (500034750129189/500000000000000 : ℝ)^8345 := by
      have hnat : (25007080586278315919 : ℕ)^2048*500000000000000^8345 ≤ 500034750129189^8345*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007080586278315919 25000000000000000000 500034750129189 500000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500034750129189/500000000000000 : ℝ)) (X := (25007080586278315919/25000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023970885606935081/50000000000000000000 : ℝ) ≤ (10001176357012953/10000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (50023970885606935081/50000000000000000000 : ℝ)^2048 ≤ (10001176357012953/10000000000000000 : ℝ)^8345 := by
      have hnat : (50023970885606935081 : ℕ)^2048*10000000000000000^8345 ≤ 10001176357012953^8345*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023970885606935081 50000000000000000000 10001176357012953 10000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001176357012953/10000000000000000 : ℝ)) (X := (50023970885606935081/50000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508445149664309581/12500000000000000000 : ℝ) ≤ (5000828855721063/5000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (12508445149664309581/12500000000000000000 : ℝ)^2048 ≤ (5000828855721063/5000000000000000 : ℝ)^8345 := by
      have hnat : (12508445149664309581 : ℕ)^2048*5000000000000000^8345 ≤ 5000828855721063^8345*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508445149664309581 12500000000000000000 5000828855721063 5000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000828855721063/5000000000000000 : ℝ)) (X := (12508445149664309581/12500000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7080586278315919/50000000000000000000 : ℝ) ≤ ((1929352897260121761/1930000000000000000 : ℝ)+2*(481354429173/270200000000000 : ℝ)*(11361/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (1929352897260121761/1930000000000000000 : ℝ)+2*(481354429173/270200000000000 : ℝ)*(11361/100000 : ℝ)=(500034750129189/500000000000000 : ℝ) by norm_num, show 1+2*(7080586278315919/50000000000000000000 : ℝ)=(25007080586278315919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8445149664309581/25000000000000000000 : ℝ)+(7080586278315919/50000000000000000000 : ℝ) ≤ ((1929352897260121761/1930000000000000000 : ℝ)+(481354429173/270200000000000 : ℝ)*((14063/100000 : ℝ)+(11361/100000 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (1929352897260121761/1930000000000000000 : ℝ)+(481354429173/270200000000000 : ℝ)*((14063/100000 : ℝ)+(11361/100000 : ℝ))=(10001176357012953/10000000000000000 : ℝ) by norm_num, show 1+(8445149664309581/25000000000000000000 : ℝ)+(7080586278315919/50000000000000000000 : ℝ)=(50023970885606935081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8445149664309581/25000000000000000000 : ℝ) ≤ ((1929352897260121761/1930000000000000000 : ℝ)+2*(481354429173/270200000000000 : ℝ)*(14063/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (1929352897260121761/1930000000000000000 : ℝ)+2*(481354429173/270200000000000 : ℝ)*(14063/100000 : ℝ)=(5000828855721063/5000000000000000 : ℝ) by norm_num, show 1+2*(8445149664309581/25000000000000000000 : ℝ)=(12508445149664309581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1929352897260121761/1930000000000000000 : ℝ)*(X 1 0+X 2 0)+(481354429173/270200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (1929352897260121761/1930000000000000000 : ℝ)) (alpha := (481354429173/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1929352897260121761/1930000000000000000 : ℝ)*(X 0 1+X 2 1)+(481354429173/270200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (1929352897260121761/1930000000000000000 : ℝ)) (alpha := (481354429173/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1929352897260121761/1930000000000000000 : ℝ)*(X 0 2+X 1 2)+(481354429173/270200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (1929352897260121761/1930000000000000000 : ℝ)) (alpha := (481354429173/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080816021/5000000000 : ℝ)*X 0 0+(16852683/31250000 : ℝ)*X 0 1+(20569903/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344723191/10000000000 : ℝ)*X 1 0+(-2226027461/10000000000 : ℝ)*X 1 1+(2632947713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668090457/1250000000 : ℝ)*X 2 0+(5265895001/10000000000 : ℝ)*X 2 1+(-445205481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218156231/500000000 : ℝ)*X 0 0+(423837927/1000000000 : ℝ)*X 0 1+(4491514203/10000000000 : ℝ)*X 0 2+(218156231/500000000 : ℝ)*X 1 0+(423837927/1000000000 : ℝ)*X 1 1+(4491514203/10000000000 : ℝ)*X 1 2+(218156231/500000000 : ℝ)*X 2 0+(423837927/1000000000 : ℝ)*X 2 1+(4491514203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86465469/400000000 : ℝ)*X 0 0+(131655363/250000000 : ℝ)*X 0 1+(1348134547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312530473/10000000000 : ℝ)*X 1 0+(-2099384489/10000000000 : ℝ)*X 1 1+(1348134547/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664066309/1250000000 : ℝ)*X 2 0+(5392538189/10000000000 : ℝ)*X 2 1+(-2099384489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363134343/10000000000 : ℝ)*X 0 0+(4490877887/10000000000 : ℝ)*X 0 1+(4239017857/10000000000 : ℝ)*X 0 2+(4363134343/10000000000 : ℝ)*X 1 0+(4490877887/10000000000 : ℝ)*X 1 1+(4239017857/10000000000 : ℝ)*X 1 2+(4363134343/10000000000 : ℝ)*X 2 0+(4490877887/10000000000 : ℝ)*X 2 1+(4239017857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2536744887647223210033218367/675500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (934622251/100000000000000 : ℝ)*(base19) + (1385032097/100000000000000 : ℝ)*(base23) + (119378997/100000000000000 : ℝ)*(upper3) + (62759441/50000000000000 : ℝ)*(upper4) + (83256439/50000000000000 : ℝ)*(upper5) + (5913422202603169/100000000000000 : ℝ)*(major0) + (5913422202603169/100000000000000 : ℝ)*(major1) + (5913422202603169/100000000000000 : ℝ)*(major2) + (7876314167282497/100000000000000 : ℝ)*(sp0) + (7876354789702039/100000000000000 : ℝ)*(sp1) + (7876354339292193/100000000000000 : ℝ)*(sp2) + (987618362538201/25000000000000 : ℝ)*(sp3) + (41557041793/100000000000000 : ℝ)*(sp4) + (15105550603/100000000000000 : ℝ)*(sp7) + (1975244277851703/50000000000000 : ℝ)*(f.failure) + (787635572432429/10000000000000 : ℝ)*(f.sum) + (46188418199137/13510000000000000000000000000 : ℝ)*base65 + (19229385046777925737/1351000000000000000000000000000000 : ℝ)*base68 + (18574164829419925737/1351000000000000000000000000000000 : ℝ)*base70 + (27154664663864925737/1351000000000000000000000000000000 : ℝ)*base72 + (33223624597383/13510000000000000000000000000 : ℝ)*base74 + (25822560883353925737/1351000000000000000000000000000000 : ℝ)*base76 + (24992971659673925737/1351000000000000000000000000000000 : ℝ)*base78 + (49720061507840925737/1351000000000000000000000000000000 : ℝ)*base80 + (29756254131943/13510000000000000000000000000 : ℝ)*base82 + (18756031/5000000000000000000000 : ℝ)*base89 + (18756031/5000000000000000000000 : ℝ)*base91 + (18756031/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3763030437814068563458329/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394197147/50000000000000 : ℝ)*(base19) + (6679959/781250000000 : ℝ)*(base23) + (86806603/100000000000000 : ℝ)*(upper3) + (30977229/100000000000000 : ℝ)*(lower4) + (21970987/25000000000000 : ℝ)*(upper5) + (1485828910736763/25000000000000 : ℝ)*(major0) + (1485828910736763/25000000000000 : ℝ)*(major1) + (1485828910736763/25000000000000 : ℝ)*(major2) + (2728571409/12500000000000 : ℝ)*(sp1) + (5862222083/25000000000000 : ℝ)*(sp2) + (3958086069133631/50000000000000 : ℝ)*(sp4) + (123689836270339/1562500000000 : ℝ)*(sp5) + (7916147834344179/100000000000000 : ℝ)*(sp6) + (992614751068323/25000000000000 : ℝ)*(sp7) + (992614751068323/25000000000000 : ℝ)*(f.failure) + (3958086069133631/50000000000000 : ℝ)*(f.sum) + (6810901166883/1688750000000000000000000000 : ℝ)*base66 + (1654306009631947501/337750000000000000000000000000000 : ℝ)*base67 + (4409590038667947501/337750000000000000000000000000000 : ℝ)*base69 + (2319477590313947501/337750000000000000000000000000000 : ℝ)*base71 + (18112290118171/3377500000000000000000000000 : ℝ)*base74 + (995682422298052499/337750000000000000000000000000000 : ℝ)*base76 + (3152114724033947501/337750000000000000000000000000000 : ℝ)*base77 + (3320189448361302499/337750000000000000000000000000000 : ℝ)*base80 + (5093466870017/6755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14018229/2500000000000000000000 : ℝ)*base90 + (14018229/2500000000000000000000 : ℝ)*base92 + (14018229/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1153_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1153_s8_0 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161639731/10000000000 : ℝ)*x 0 + (5392792487/10000000000 : ℝ)*x 1 + (2632977999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161639731/10000000000 : ℝ)^4173 ≤ (2627219868557/20000000000000 : ℝ)^3149 := by
    have hnat : (2161639731 : ℕ)^4173*20000000000000^3149 ≤ 2627219868557^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161639731 10000000000 2627219868557 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392792487/10000000000 : ℝ)^4173 ≤ (22058409695061/50000000000000 : ℝ)^3149 := by
    have hnat : (5392792487 : ℕ)^4173*50000000000000^3149 ≤ 22058409695061^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392792487 10000000000 22058409695061 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632977999/5000000000 : ℝ)^4173 ≤ (42747081248461/100000000000000 : ℝ)^3149 := by
    have hnat : (2632977999 : ℕ)^4173*100000000000000^3149 ≤ 42747081248461^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632977999 5000000000 42747081248461 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161639731/10000000000 : ℝ), (5392792487/10000000000 : ℝ), (2632977999/5000000000 : ℝ)] ![(2627219868557/20000000000000 : ℝ), (22058409695061/50000000000000 : ℝ), (42747081248461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161639731/10000000000 : ℝ)|^4173 ≤ (2627219868557/20000000000000 : ℝ)^3149
        have hw : |(-2161639731/10000000000 : ℝ)|=(2161639731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392792487/10000000000 : ℝ)|^4173 ≤ (22058409695061/50000000000000 : ℝ)^3149
        have hw : |(5392792487/10000000000 : ℝ)|=(5392792487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632977999/5000000000 : ℝ)|^4173 ≤ (42747081248461/100000000000000 : ℝ)^3149
        have hw : |(2632977999/5000000000 : ℝ)|=(2632977999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_1 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344706091/10000000000 : ℝ)*x 0 + (-89038801/400000000 : ℝ)*x 1 + (2632978009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344706091/10000000000 : ℝ)^4173 ≤ (42574488119/97656250000 : ℝ)^3149 := by
    have hnat : (5344706091 : ℕ)^4173*97656250000^3149 ≤ 42574488119^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344706091 10000000000 42574488119 97656250000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89038801/400000000 : ℝ)^4173 ≤ (6828321344323/50000000000000 : ℝ)^3149 := by
    have hnat : (89038801 : ℕ)^4173*50000000000000^3149 ≤ 6828321344323^3149*400000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89038801 400000000 6828321344323 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632978009/5000000000 : ℝ)^4173 ≤ (5343385182951/12500000000000 : ℝ)^3149 := by
    have hnat : (2632978009 : ℕ)^4173*12500000000000^3149 ≤ 5343385182951^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632978009 5000000000 5343385182951 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344706091/10000000000 : ℝ), (-89038801/400000000 : ℝ), (2632978009/5000000000 : ℝ)] ![(42574488119/97656250000 : ℝ), (6828321344323/50000000000000 : ℝ), (5343385182951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344706091/10000000000 : ℝ)|^4173 ≤ (42574488119/97656250000 : ℝ)^3149
        have hw : |(5344706091/10000000000 : ℝ)|=(5344706091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89038801/400000000 : ℝ)|^4173 ≤ (6828321344323/50000000000000 : ℝ)^3149
        have hw : |(-89038801/400000000 : ℝ)|=(89038801/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632978009/5000000000 : ℝ)|^4173 ≤ (5343385182951/12500000000000 : ℝ)^3149
        have hw : |(2632978009/5000000000 : ℝ)|=(2632978009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_2 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53447061/100000000 : ℝ)*x 0 + (5265956009/10000000000 : ℝ)*x 1 + (-89038801/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53447061/100000000 : ℝ)^4173 ≤ (2179813796557/5000000000000 : ℝ)^3149 := by
    have hnat : (53447061 : ℕ)^4173*5000000000000^3149 ≤ 2179813796557^3149*100000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53447061 100000000 2179813796557 5000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265956009/10000000000 : ℝ)^4173 ≤ (5343385170849/12500000000000 : ℝ)^3149 := by
    have hnat : (5265956009 : ℕ)^4173*12500000000000^3149 ≤ 5343385170849^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265956009 10000000000 5343385170849 12500000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89038801/400000000 : ℝ)^4173 ≤ (6828321344323/50000000000000 : ℝ)^3149 := by
    have hnat : (89038801 : ℕ)^4173*50000000000000^3149 ≤ 6828321344323^3149*400000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89038801 400000000 6828321344323 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53447061/100000000 : ℝ), (5265956009/10000000000 : ℝ), (-89038801/400000000 : ℝ)] ![(2179813796557/5000000000000 : ℝ), (5343385170849/12500000000000 : ℝ), (6828321344323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53447061/100000000 : ℝ)|^4173 ≤ (2179813796557/5000000000000 : ℝ)^3149
        have hw : |(53447061/100000000 : ℝ)|=(53447061/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265956009/10000000000 : ℝ)|^4173 ≤ (5343385170849/12500000000000 : ℝ)^3149
        have hw : |(5265956009/10000000000 : ℝ)|=(5265956009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89038801/400000000 : ℝ)|^4173 ≤ (6828321344323/50000000000000 : ℝ)^3149
        have hw : |(-89038801/400000000 : ℝ)|=(89038801/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_3 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363127863/10000000000 : ℝ)*x 0 + (847701021/2000000000 : ℝ)*x 1 + (2245693753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363127863/10000000000 : ℝ)^4173 ≤ (16658523400173/50000000000000 : ℝ)^3149 := by
    have hnat : (4363127863 : ℕ)^4173*50000000000000^3149 ≤ 16658523400173^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363127863 10000000000 16658523400173 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847701021/2000000000 : ℝ)^4173 ≤ (16030932141467/50000000000000 : ℝ)^3149 := by
    have hnat : (847701021 : ℕ)^4173*50000000000000^3149 ≤ 16030932141467^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847701021 2000000000 16030932141467 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245693753/5000000000 : ℝ)^4173 ≤ (17310544451161/50000000000000 : ℝ)^3149 := by
    have hnat : (2245693753 : ℕ)^4173*50000000000000^3149 ≤ 17310544451161^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245693753 5000000000 17310544451161 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363127863/10000000000 : ℝ), (847701021/2000000000 : ℝ), (2245693753/5000000000 : ℝ)] ![(16658523400173/50000000000000 : ℝ), (16030932141467/50000000000000 : ℝ), (17310544451161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363127863/10000000000 : ℝ)|^4173 ≤ (16658523400173/50000000000000 : ℝ)^3149
        have hw : |(4363127863/10000000000 : ℝ)|=(4363127863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847701021/2000000000 : ℝ)|^4173 ≤ (16030932141467/50000000000000 : ℝ)^3149
        have hw : |(847701021/2000000000 : ℝ)|=(847701021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245693753/5000000000 : ℝ)|^4173 ≤ (17310544451161/50000000000000 : ℝ)^3149
        have hw : |(2245693753/5000000000 : ℝ)|=(2245693753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_4 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080822267/5000000000 : ℝ)*x 0 + (2633137289/5000000000 : ℝ)*x 1 + (539247279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080822267/5000000000 : ℝ)^4173 ≤ (13136138021459/100000000000000 : ℝ)^3149 := by
    have hnat : (1080822267 : ℕ)^4173*100000000000000^3149 ≤ 13136138021459^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080822267 5000000000 13136138021459 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633137289/5000000000 : ℝ)^4173 ≤ (42750508356097/100000000000000 : ℝ)^3149 := by
    have hnat : (2633137289 : ℕ)^4173*100000000000000^3149 ≤ 42750508356097^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633137289 5000000000 42750508356097 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539247279/1000000000 : ℝ)^4173 ≤ (44113353613371/100000000000000 : ℝ)^3149 := by
    have hnat : (539247279 : ℕ)^4173*100000000000000^3149 ≤ 44113353613371^3149*1000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539247279 1000000000 44113353613371 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080822267/5000000000 : ℝ), (2633137289/5000000000 : ℝ), (539247279/1000000000 : ℝ)] ![(13136138021459/100000000000000 : ℝ), (42750508356097/100000000000000 : ℝ), (44113353613371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080822267/5000000000 : ℝ)|^4173 ≤ (13136138021459/100000000000000 : ℝ)^3149
        have hw : |(-1080822267/5000000000 : ℝ)|=(1080822267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633137289/5000000000 : ℝ)|^4173 ≤ (42750508356097/100000000000000 : ℝ)^3149
        have hw : |(2633137289/5000000000 : ℝ)|=(2633137289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539247279/1000000000 : ℝ)|^4173 ≤ (44113353613371/100000000000000 : ℝ)^3149
        have hw : |(539247279/1000000000 : ℝ)|=(539247279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_5 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062509061/2000000000 : ℝ)*x 0 + (-65607917/312500000 : ℝ)*x 1 + (5392472763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062509061/2000000000 : ℝ)^4173 ≤ (8649795570489/20000000000000 : ℝ)^3149 := by
    have hnat : (1062509061 : ℕ)^4173*20000000000000^3149 ≤ 8649795570489^3149*2000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062509061 2000000000 8649795570489 20000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65607917/312500000 : ℝ)^4173 ≤ (1263766881583/10000000000000 : ℝ)^3149 := by
    have hnat : (65607917 : ℕ)^4173*10000000000000^3149 ≤ 1263766881583^3149*312500000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65607917 312500000 1263766881583 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392472763/10000000000 : ℝ)^4173 ≤ (1378542291271/3125000000000 : ℝ)^3149 := by
    have hnat : (5392472763 : ℕ)^4173*3125000000000^3149 ≤ 1378542291271^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392472763 10000000000 1378542291271 3125000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062509061/2000000000 : ℝ), (-65607917/312500000 : ℝ), (5392472763/10000000000 : ℝ)] ![(8649795570489/20000000000000 : ℝ), (1263766881583/10000000000000 : ℝ), (1378542291271/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062509061/2000000000 : ℝ)|^4173 ≤ (8649795570489/20000000000000 : ℝ)^3149
        have hw : |(1062509061/2000000000 : ℝ)|=(1062509061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65607917/312500000 : ℝ)|^4173 ≤ (1263766881583/10000000000000 : ℝ)^3149
        have hw : |(-65607917/312500000 : ℝ)|=(65607917/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392472763/10000000000 : ℝ)|^4173 ≤ (1378542291271/3125000000000 : ℝ)^3149
        have hw : |(5392472763/10000000000 : ℝ)|=(5392472763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_6 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656272687/5000000000 : ℝ)*x 0 + (674059091/1250000000 : ℝ)*x 1 + (-1049726649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656272687/5000000000 : ℝ)^4173 ≤ (4324897859683/10000000000000 : ℝ)^3149 := by
    have hnat : (2656272687 : ℕ)^4173*10000000000000^3149 ≤ 4324897859683^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656272687 5000000000 4324897859683 10000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674059091/1250000000 : ℝ)^4173 ≤ (44113352941247/100000000000000 : ℝ)^3149 := by
    have hnat : (674059091 : ℕ)^4173*100000000000000^3149 ≤ 44113352941247^3149*1250000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674059091 1250000000 44113352941247 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049726649/5000000000 : ℝ)^4173 ≤ (12637668448891/100000000000000 : ℝ)^3149 := by
    have hnat : (1049726649 : ℕ)^4173*100000000000000^3149 ≤ 12637668448891^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049726649 5000000000 12637668448891 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656272687/5000000000 : ℝ), (674059091/1250000000 : ℝ), (-1049726649/5000000000 : ℝ)] ![(4324897859683/10000000000000 : ℝ), (44113352941247/100000000000000 : ℝ), (12637668448891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656272687/5000000000 : ℝ)|^4173 ≤ (4324897859683/10000000000000 : ℝ)^3149
        have hw : |(2656272687/5000000000 : ℝ)|=(2656272687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674059091/1250000000 : ℝ)|^4173 ≤ (44113352941247/100000000000000 : ℝ)^3149
        have hw : |(674059091/1250000000 : ℝ)|=(674059091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049726649/5000000000 : ℝ)|^4173 ≤ (12637668448891/100000000000000 : ℝ)^3149
        have hw : |(-1049726649/5000000000 : ℝ)|=(1049726649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1153_s8_7 (p : ℝ) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363137511/10000000000 : ℝ)*x 0 + (2245376149/5000000000 : ℝ)*x 1 + (2119571313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363137511/10000000000 : ℝ)^4173 ≤ (8329286107499/25000000000000 : ℝ)^3149 := by
    have hnat : (4363137511 : ℕ)^4173*25000000000000^3149 ≤ 8329286107499^3149*10000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363137511 10000000000 8329286107499 25000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245376149/5000000000 : ℝ)^4173 ≤ (34614600438421/100000000000000 : ℝ)^3149 := by
    have hnat : (2245376149 : ℕ)^4173*100000000000000^3149 ≤ 34614600438421^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245376149 5000000000 34614600438421 100000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119571313/5000000000 : ℝ)^4173 ≤ (16034127553783/50000000000000 : ℝ)^3149 := by
    have hnat : (2119571313 : ℕ)^4173*50000000000000^3149 ≤ 16034127553783^3149*5000000000^4173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119571313 5000000000 16034127553783 50000000000000 4173 3149 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4173/1024 : ℝ)) 4173 3149 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363137511/10000000000 : ℝ), (2245376149/5000000000 : ℝ), (2119571313/5000000000 : ℝ)] ![(8329286107499/25000000000000 : ℝ), (34614600438421/100000000000000 : ℝ), (16034127553783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363137511/10000000000 : ℝ)|^4173 ≤ (8329286107499/25000000000000 : ℝ)^3149
        have hw : |(4363137511/10000000000 : ℝ)|=(4363137511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245376149/5000000000 : ℝ)|^4173 ≤ (34614600438421/100000000000000 : ℝ)^3149
        have hw : |(2245376149/5000000000 : ℝ)|=(2245376149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119571313/5000000000 : ℝ)|^4173 ≤ (16034127553783/50000000000000 : ℝ)^3149
        have hw : |(2119571313/5000000000 : ℝ)|=(2119571313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1153_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1421/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11367/100000 : ℝ) ^ (8345/2048 : ℝ) ≤ (709583568309577/5000000000000000000 : ℝ) := by
    have hpowers : (11367/100000 : ℝ)^8345 ≤ (709583568309577/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11367 : ℕ)^8345*5000000000000000000^2048 ≤ 709583568309577^2048*100000^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11367 100000 709583568309577 5000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11367/100000 : ℝ)) (X := (709583568309577/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (8345/2048 : ℝ) ≤ (1348485454546389/4000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^8345 ≤ (1348485454546389/4000000000000000000 : ℝ)^2048 := by
      have hnat : (1757 : ℕ)^8345*4000000000000000000^2048 ≤ 1348485454546389^2048*12500^8345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 1348485454546389 4000000000000000000 8345 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (1348485454546389/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500709583568309577/2500000000000000000 : ℝ) ≤ (100006964992453/100000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (2500709583568309577/2500000000000000000 : ℝ)^2048 ≤ (100006964992453/100000000000000 : ℝ)^8345 := by
      have hnat : (2500709583568309577 : ℕ)^2048*100000000000000^8345 ≤ 100006964992453^8345*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500709583568309577 2500000000000000000 100006964992453 100000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100006964992453/100000000000000 : ℝ)) (X := (2500709583568309577/2500000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009580761545970253/20000000000000000000 : ℝ) ≤ (10001175425663503/10000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (20009580761545970253/20000000000000000000 : ℝ)^2048 ≤ (10001175425663503/10000000000000000 : ℝ)^8345 := by
      have hnat : (20009580761545970253 : ℕ)^2048*10000000000000000^8345 ≤ 10001175425663503^8345*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009580761545970253 20000000000000000000 10001175425663503 10000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001175425663503/10000000000000000 : ℝ)) (X := (20009580761545970253/20000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001348485454546389/2000000000000000000 : ℝ) ≤ (5000827176040853/5000000000000000 : ℝ) ^ (8345/2048 : ℝ) := by
    have hpowers : (2001348485454546389/2000000000000000000 : ℝ)^2048 ≤ (5000827176040853/5000000000000000 : ℝ)^8345 := by
      have hnat : (2001348485454546389 : ℕ)^2048*5000000000000000^8345 ≤ 5000827176040853^8345*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001348485454546389 2000000000000000000 5000827176040853 5000000000000000 2048 8345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000827176040853/5000000000000000 : ℝ)) (X := (2001348485454546389/2000000000000000000 : ℝ)) (by norm_num) 8345 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(709583568309577/5000000000000000000 : ℝ) ≤ ((13440492486639592349/13445000000000000000 : ℝ)+2*(478926418203/268900000000000 : ℝ)*(11367/100000 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (13440492486639592349/13445000000000000000 : ℝ)+2*(478926418203/268900000000000 : ℝ)*(11367/100000 : ℝ)=(100006964992453/100000000000000 : ℝ) by norm_num, show 1+2*(709583568309577/5000000000000000000 : ℝ)=(2500709583568309577/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1348485454546389/4000000000000000000 : ℝ)+(709583568309577/5000000000000000000 : ℝ) ≤ ((13440492486639592349/13445000000000000000 : ℝ)+(478926418203/268900000000000 : ℝ)*((1757/12500 : ℝ)+(11367/100000 : ℝ)))^(8345/2048 : ℝ) := by
    rw [show (13440492486639592349/13445000000000000000 : ℝ)+(478926418203/268900000000000 : ℝ)*((1757/12500 : ℝ)+(11367/100000 : ℝ))=(10001175425663503/10000000000000000 : ℝ) by norm_num, show 1+(1348485454546389/4000000000000000000 : ℝ)+(709583568309577/5000000000000000000 : ℝ)=(20009580761545970253/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1348485454546389/4000000000000000000 : ℝ) ≤ ((13440492486639592349/13445000000000000000 : ℝ)+2*(478926418203/268900000000000 : ℝ)*(1757/12500 : ℝ))^(8345/2048 : ℝ) := by
    rw [show (13440492486639592349/13445000000000000000 : ℝ)+2*(478926418203/268900000000000 : ℝ)*(1757/12500 : ℝ)=(5000827176040853/5000000000000000 : ℝ) by norm_num, show 1+2*(1348485454546389/4000000000000000000 : ℝ)=(2001348485454546389/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13440492486639592349/13445000000000000000 : ℝ)*(X 1 0+X 2 0)+(478926418203/268900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13440492486639592349/13445000000000000000 : ℝ)) (alpha := (478926418203/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13440492486639592349/13445000000000000000 : ℝ)*(X 0 1+X 2 1)+(478926418203/268900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13440492486639592349/13445000000000000000 : ℝ)) (alpha := (478926418203/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13440492486639592349/13445000000000000000 : ℝ)*(X 0 2+X 1 2)+(478926418203/268900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8345/2048 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (13440492486639592349/13445000000000000000 : ℝ)) (alpha := (478926418203/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161639731/10000000000 : ℝ)*X 0 0+(5392792487/10000000000 : ℝ)*X 0 1+(2632977999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344706091/10000000000 : ℝ)*X 1 0+(-89038801/400000000 : ℝ)*X 1 1+(2632978009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53447061/100000000 : ℝ)*X 2 0+(5265956009/10000000000 : ℝ)*X 2 1+(-89038801/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363127863/10000000000 : ℝ)*X 0 0+(847701021/2000000000 : ℝ)*X 0 1+(2245693753/5000000000 : ℝ)*X 0 2+(4363127863/10000000000 : ℝ)*X 1 0+(847701021/2000000000 : ℝ)*X 1 1+(2245693753/5000000000 : ℝ)*X 1 2+(4363127863/10000000000 : ℝ)*X 2 0+(847701021/2000000000 : ℝ)*X 2 1+(2245693753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080822267/5000000000 : ℝ)*X 0 0+(2633137289/5000000000 : ℝ)*X 0 1+(539247279/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062509061/2000000000 : ℝ)*X 1 0+(-65607917/312500000 : ℝ)*X 1 1+(5392472763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656272687/5000000000 : ℝ)*X 2 0+(674059091/1250000000 : ℝ)*X 2 1+(-1049726649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363137511/10000000000 : ℝ)*X 0 0+(2245376149/5000000000 : ℝ)*X 0 1+(2119571313/5000000000 : ℝ)*X 0 2+(4363137511/10000000000 : ℝ)*X 1 0+(2245376149/5000000000 : ℝ)*X 1 1+(2119571313/5000000000 : ℝ)*X 1 2+(4363137511/10000000000 : ℝ)*X 2 0+(2245376149/5000000000 : ℝ)*X 2 1+(2119571313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1153_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5087267727014844888536321847/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (736887423/50000000000000 : ℝ)*(base19) + (1380167103/100000000000000 : ℝ)*(base23) + (57126411/100000000000000 : ℝ)*(lower2) + (189238073/100000000000000 : ℝ)*(upper3) + (7045677/6250000000000 : ℝ)*(upper5) + (5919350044558401/100000000000000 : ℝ)*(major0) + (5919350044558401/100000000000000 : ℝ)*(major1) + (5919350044558401/100000000000000 : ℝ)*(major2) + (7884209724457737/100000000000000 : ℝ)*(sp0) + (315369987426033/4000000000000 : ℝ)*(sp1) + (985531222407321/12500000000000 : ℝ)*(sp2) + (3954426808143753/100000000000000 : ℝ)*(sp3) + (41434967933/100000000000000 : ℝ)*(sp4) + (10934648291/50000000000000 : ℝ)*(sp7) + (1977224338720167/50000000000000 : ℝ)*(f.failure) + (7884251159425671/100000000000000 : ℝ)*(f.sum) + (95720947183637/13445000000000000000000000000 : ℝ)*base66 + (5674218595450423949/1344500000000000000000000000000000 : ℝ)*base67 + (2314693183363576051/1344500000000000000000000000000000 : ℝ)*base70 + (21032416641828576051/1344500000000000000000000000000000 : ℝ)*base72 + (34827534260583/13445000000000000000000000000 : ℝ)*base73 + (28502481342366576051/1344500000000000000000000000000000 : ℝ)*base76 + (37422126727091076051/1344500000000000000000000000000000 : ℝ)*base78 + (6106332937354923949/1344500000000000000000000000000000 : ℝ)*base79 + (52062057606653/13445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5398959/5000000000000000000000 : ℝ)*base89 + (5398959/5000000000000000000000 : ℝ)*base91 + (5398959/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5652844915847307841930850709/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1239118417/100000000000000 : ℝ)*(base19) + (193274233/12500000000000 : ℝ)*(base23) + (17834163/4000000000000 : ℝ)*(lower1) + (103678293/100000000000000 : ℝ)*(upper3) + (11473767/12500000000000 : ℝ)*(lower4) + (94358887/50000000000000 : ℝ)*(upper5) + (5949200363798547/100000000000000 : ℝ)*(major0) + (5949200363798547/100000000000000 : ℝ)*(major1) + (5949200363798547/100000000000000 : ℝ)*(major2) + (259157809/5000000000000 : ℝ)*(sp2) + (3962005064270607/50000000000000 : ℝ)*(sp4) + (7924008889422797/100000000000000 : ℝ)*(sp5) + (7924003399191169/100000000000000 : ℝ)*(sp6) + (1987195159380527/50000000000000 : ℝ)*(sp7) + (1987195159380527/50000000000000 : ℝ)*(f.failure) + (3962005064270607/50000000000000 : ℝ)*(f.sum) + (63508804564469/13445000000000000000000000000 : ℝ)*base66 + (140348502682797433097/1344500000000000000000000000000000 : ℝ)*base68 + (7238075632142566903/1344500000000000000000000000000000 : ℝ)*base69 + (299714850489124933097/1344500000000000000000000000000000 : ℝ)*base72 + (80951715817861/13445000000000000000000000000 : ℝ)*base73 + (138024029374073066903/1344500000000000000000000000000000 : ℝ)*base75 + (15150056950809433097/1344500000000000000000000000000000 : ℝ)*base78 + (6213071260517433097/1344500000000000000000000000000000 : ℝ)*base80 + (70776978279149/13445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (62034679/5000000000000000000000 : ℝ)*base89 + (62034679/5000000000000000000000 : ℝ)*base91 + (62034679/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1153_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1153_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1153_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1153_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1153_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1153_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8345/2048 : ℝ) ≤ p) (hpb : p ≤ (4173/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149688377/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1153_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
