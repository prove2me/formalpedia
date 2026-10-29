-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:48.812659+00:00
-- url     : https://prove2.me/submissions/19d3aeea-2e85-463f-b7cd-78f75e201bd4

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c305063_s3_s3_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-128333351/2000000000 : ℝ)*x 0 + (2827268297/5000000000 : ℝ)*x 1 + (5900492111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128333351/2000000000 : ℝ)^67 ≤ (542203273193/20000000000000 : ℝ)^51 := by
    have hnat : (128333351 : ℕ)^67*20000000000000^51 ≤ 542203273193^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128333351 2000000000 542203273193 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827268297/5000000000 : ℝ)^67 ≤ (23642187470843/50000000000000 : ℝ)^51 := by
    have hnat : (2827268297 : ℕ)^67*50000000000000^51 ≤ 23642187470843^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827268297 5000000000 23642187470843 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5900492111/10000000000 : ℝ)^67 ≤ (25002304339107/50000000000000 : ℝ)^51 := by
    have hnat : (5900492111 : ℕ)^67*50000000000000^51 ≤ 25002304339107^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5900492111 10000000000 25002304339107 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128333351/2000000000 : ℝ), (2827268297/5000000000 : ℝ), (5900492111/10000000000 : ℝ)] ![(542203273193/20000000000000 : ℝ), (23642187470843/50000000000000 : ℝ), (25002304339107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128333351/2000000000 : ℝ)|^67 ≤ (542203273193/20000000000000 : ℝ)^51
        have hw : |(-128333351/2000000000 : ℝ)|=(128333351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827268297/5000000000 : ℝ)|^67 ≤ (23642187470843/50000000000000 : ℝ)^51
        have hw : |(2827268297/5000000000 : ℝ)|=(2827268297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5900492111/10000000000 : ℝ)|^67 ≤ (25002304339107/50000000000000 : ℝ)^51
        have hw : |(5900492111/10000000000 : ℝ)|=(5900492111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5654576803/10000000000 : ℝ)*x 0 + (-642524647/10000000000 : ℝ)*x 1 + (2950012323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5654576803/10000000000 : ℝ)^67 ≤ (5910602082959/12500000000000 : ℝ)^51 := by
    have hnat : (5654576803 : ℕ)^67*12500000000000^51 ≤ 5910602082959^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654576803 10000000000 5910602082959 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642524647/10000000000 : ℝ)^67 ≤ (1357889520163/50000000000000 : ℝ)^51 := by
    have hnat : (642524647 : ℕ)^67*50000000000000^51 ≤ 1357889520163^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642524647 10000000000 1357889520163 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950012323/5000000000 : ℝ)^67 ≤ (9999880856937/20000000000000 : ℝ)^51 := by
    have hnat : (2950012323 : ℕ)^67*20000000000000^51 ≤ 9999880856937^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950012323 5000000000 9999880856937 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5654576803/10000000000 : ℝ), (-642524647/10000000000 : ℝ), (2950012323/5000000000 : ℝ)] ![(5910602082959/12500000000000 : ℝ), (1357889520163/50000000000000 : ℝ), (9999880856937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5654576803/10000000000 : ℝ)|^67 ≤ (5910602082959/12500000000000 : ℝ)^51
        have hw : |(5654576803/10000000000 : ℝ)|=(5654576803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-642524647/10000000000 : ℝ)|^67 ≤ (1357889520163/50000000000000 : ℝ)^51
        have hw : |(-642524647/10000000000 : ℝ)|=(642524647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2950012323/5000000000 : ℝ)|^67 ≤ (9999880856937/20000000000000 : ℝ)^51
        have hw : |(2950012323/5000000000 : ℝ)|=(2950012323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1431476319/2500000000 : ℝ)*x 0 + (5866425529/10000000000 : ℝ)*x 1 + (-141750469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1431476319/2500000000 : ℝ)^67 ≤ (48069953201487/100000000000000 : ℝ)^51 := by
    have hnat : (1431476319 : ℕ)^67*100000000000000^51 ≤ 48069953201487^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431476319 2500000000 48069953201487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5866425529/10000000000 : ℝ)^67 ≤ (49625676951161/100000000000000 : ℝ)^51 := by
    have hnat : (5866425529 : ℕ)^67*100000000000000^51 ≤ 49625676951161^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5866425529 10000000000 49625676951161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141750469/2500000000 : ℝ)^67 ≤ (92174793241/4000000000000 : ℝ)^51 := by
    have hnat : (141750469 : ℕ)^67*4000000000000^51 ≤ 92174793241^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141750469 2500000000 92174793241 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1431476319/2500000000 : ℝ), (5866425529/10000000000 : ℝ), (-141750469/2500000000 : ℝ)] ![(48069953201487/100000000000000 : ℝ), (49625676951161/100000000000000 : ℝ), (92174793241/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1431476319/2500000000 : ℝ)|^67 ≤ (48069953201487/100000000000000 : ℝ)^51
        have hw : |(1431476319/2500000000 : ℝ)|=(1431476319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5866425529/10000000000 : ℝ)|^67 ≤ (49625676951161/100000000000000 : ℝ)^51
        have hw : |(5866425529/10000000000 : ℝ)|=(5866425529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141750469/2500000000 : ℝ)|^67 ≤ (92174793241/4000000000000 : ℝ)^51
        have hw : |(-141750469/2500000000 : ℝ)|=(141750469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2339748319/5000000000 : ℝ)*x 0 + (4374929829/10000000000 : ℝ)*x 1 + (3935270519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2339748319/5000000000 : ℝ)^67 ≤ (36875014774581/100000000000000 : ℝ)^51 := by
    have hnat : (2339748319 : ℕ)^67*100000000000000^51 ≤ 36875014774581^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339748319 5000000000 36875014774581 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374929829/10000000000 : ℝ)^67 ≤ (33754724782369/100000000000000 : ℝ)^51 := by
    have hnat : (4374929829 : ℕ)^67*100000000000000^51 ≤ 33754724782369^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374929829 10000000000 33754724782369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3935270519/10000000000 : ℝ)^67 ≤ (1468513021259/5000000000000 : ℝ)^51 := by
    have hnat : (3935270519 : ℕ)^67*5000000000000^51 ≤ 1468513021259^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935270519 10000000000 1468513021259 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2339748319/5000000000 : ℝ), (4374929829/10000000000 : ℝ), (3935270519/10000000000 : ℝ)] ![(36875014774581/100000000000000 : ℝ), (33754724782369/100000000000000 : ℝ), (1468513021259/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2339748319/5000000000 : ℝ)|^67 ≤ (36875014774581/100000000000000 : ℝ)^51
        have hw : |(2339748319/5000000000 : ℝ)|=(2339748319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4374929829/10000000000 : ℝ)|^67 ≤ (33754724782369/100000000000000 : ℝ)^51
        have hw : |(4374929829/10000000000 : ℝ)|=(4374929829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3935270519/10000000000 : ℝ)|^67 ≤ (1468513021259/5000000000000 : ℝ)^51
        have hw : |(3935270519/10000000000 : ℝ)|=(3935270519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-939768723/10000000000 : ℝ)*x 0 + (1476964337/5000000000 : ℝ)*x 1 + (8063977951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939768723/10000000000 : ℝ)^67 ≤ (1118849059873/25000000000000 : ℝ)^51 := by
    have hnat : (939768723 : ℕ)^67*25000000000000^51 ≤ 1118849059873^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939768723 10000000000 1118849059873 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1476964337/5000000000 : ℝ)^67 ≤ (4029776705441/20000000000000 : ℝ)^51 := by
    have hnat : (1476964337 : ℕ)^67*20000000000000^51 ≤ 4029776705441^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476964337 5000000000 4029776705441 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8063977951/10000000000 : ℝ)^67 ≤ (75375720220957/100000000000000 : ℝ)^51 := by
    have hnat : (8063977951 : ℕ)^67*100000000000000^51 ≤ 75375720220957^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8063977951 10000000000 75375720220957 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939768723/10000000000 : ℝ), (1476964337/5000000000 : ℝ), (8063977951/10000000000 : ℝ)] ![(1118849059873/25000000000000 : ℝ), (4029776705441/20000000000000 : ℝ), (75375720220957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939768723/10000000000 : ℝ)|^67 ≤ (1118849059873/25000000000000 : ℝ)^51
        have hw : |(-939768723/10000000000 : ℝ)|=(939768723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1476964337/5000000000 : ℝ)|^67 ≤ (4029776705441/20000000000000 : ℝ)^51
        have hw : |(1476964337/5000000000 : ℝ)|=(1476964337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8063977951/10000000000 : ℝ)|^67 ≤ (75375720220957/100000000000000 : ℝ)^51
        have hw : |(8063977951/10000000000 : ℝ)|=(8063977951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (423981011/1250000000 : ℝ)*x 0 + (-169067873/10000000000 : ℝ)*x 1 + (2015847931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423981011/1250000000 : ℝ)^67 ≤ (4832282504241/20000000000000 : ℝ)^51 := by
    have hnat : (423981011 : ℕ)^67*20000000000000^51 ≤ 4832282504241^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423981011 1250000000 4832282504241 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169067873/10000000000 : ℝ)^67 ≤ (235032916543/50000000000000 : ℝ)^51 := by
    have hnat : (169067873 : ℕ)^67*50000000000000^51 ≤ 235032916543^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169067873 10000000000 235032916543 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015847931/2500000000 : ℝ)^67 ≤ (18842130406929/25000000000000 : ℝ)^51 := by
    have hnat : (2015847931 : ℕ)^67*25000000000000^51 ≤ 18842130406929^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015847931 2500000000 18842130406929 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423981011/1250000000 : ℝ), (-169067873/10000000000 : ℝ), (2015847931/2500000000 : ℝ)] ![(4832282504241/20000000000000 : ℝ), (235032916543/50000000000000 : ℝ), (18842130406929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423981011/1250000000 : ℝ)|^67 ≤ (4832282504241/20000000000000 : ℝ)^51
        have hw : |(423981011/1250000000 : ℝ)|=(423981011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169067873/10000000000 : ℝ)|^67 ≤ (235032916543/50000000000000 : ℝ)^51
        have hw : |(-169067873/10000000000 : ℝ)|=(169067873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015847931/2500000000 : ℝ)|^67 ≤ (18842130406929/25000000000000 : ℝ)^51
        have hw : |(2015847931/2500000000 : ℝ)|=(2015847931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (412700343/1250000000 : ℝ)*x 0 + (8164554431/10000000000 : ℝ)*x 1 + (-38109399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412700343/1250000000 : ℝ)^67 ≤ (23320428391081/100000000000000 : ℝ)^51 := by
    have hnat : (412700343 : ℕ)^67*100000000000000^51 ≤ 23320428391081^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412700343 1250000000 23320428391081 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8164554431/10000000000 : ℝ)^67 ≤ (76613175853379/100000000000000 : ℝ)^51 := by
    have hnat : (8164554431 : ℕ)^67*100000000000000^51 ≤ 76613175853379^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8164554431 10000000000 76613175853379 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38109399/10000000000 : ℝ)^67 ≤ (1659893477/2500000000000 : ℝ)^51 := by
    have hnat : (38109399 : ℕ)^67*2500000000000^51 ≤ 1659893477^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38109399 10000000000 1659893477 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412700343/1250000000 : ℝ), (8164554431/10000000000 : ℝ), (-38109399/10000000000 : ℝ)] ![(23320428391081/100000000000000 : ℝ), (76613175853379/100000000000000 : ℝ), (1659893477/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412700343/1250000000 : ℝ)|^67 ≤ (23320428391081/100000000000000 : ℝ)^51
        have hw : |(412700343/1250000000 : ℝ)|=(412700343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8164554431/10000000000 : ℝ)|^67 ≤ (76613175853379/100000000000000 : ℝ)^51
        have hw : |(8164554431/10000000000 : ℝ)|=(8164554431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38109399/10000000000 : ℝ)|^67 ≤ (1659893477/2500000000000 : ℝ)^51
        have hw : |(-38109399/10000000000 : ℝ)|=(38109399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3383909279/10000000000 : ℝ)*x 0 + (1809426011/2500000000 : ℝ)*x 1 + (1800743659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3383909279/10000000000 : ℝ)^67 ≤ (6021786788063/25000000000000 : ℝ)^51 := by
    have hnat : (3383909279 : ℕ)^67*25000000000000^51 ≤ 6021786788063^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383909279 10000000000 6021786788063 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1809426011/2500000000 : ℝ)^67 ≤ (32698213362819/50000000000000 : ℝ)^51 := by
    have hnat : (1809426011 : ℕ)^67*50000000000000^51 ≤ 32698213362819^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809426011 2500000000 32698213362819 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800743659/10000000000 : ℝ)^67 ≤ (10516426108101/100000000000000 : ℝ)^51 := by
    have hnat : (1800743659 : ℕ)^67*100000000000000^51 ≤ 10516426108101^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800743659 10000000000 10516426108101 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3383909279/10000000000 : ℝ), (1809426011/2500000000 : ℝ), (1800743659/10000000000 : ℝ)] ![(6021786788063/25000000000000 : ℝ), (32698213362819/50000000000000 : ℝ), (10516426108101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3383909279/10000000000 : ℝ)|^67 ≤ (6021786788063/25000000000000 : ℝ)^51
        have hw : |(3383909279/10000000000 : ℝ)|=(3383909279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1809426011/2500000000 : ℝ)|^67 ≤ (32698213362819/50000000000000 : ℝ)^51
        have hw : |(1809426011/2500000000 : ℝ)|=(1809426011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1800743659/10000000000 : ℝ)|^67 ≤ (10516426108101/100000000000000 : ℝ)^51
        have hw : |(1800743659/10000000000 : ℝ)|=(1800743659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-127129329/10000000000 : ℝ)*x 0 + (660671959/2000000000 : ℝ)*x 1 + (4071194403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127129329/10000000000 : ℝ)^67 ≤ (161610408939/50000000000000 : ℝ)^51 := by
    have hnat : (127129329 : ℕ)^67*50000000000000^51 ≤ 161610408939^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127129329 10000000000 161610408939 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660671959/2000000000 : ℝ)^67 ≤ (4667346799461/20000000000000 : ℝ)^51 := by
    have hnat : (660671959 : ℕ)^67*20000000000000^51 ≤ 4667346799461^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660671959 2000000000 4667346799461 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4071194403/5000000000 : ℝ)^67 ≤ (19085011294013/25000000000000 : ℝ)^51 := by
    have hnat : (4071194403 : ℕ)^67*25000000000000^51 ≤ 19085011294013^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4071194403 5000000000 19085011294013 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127129329/10000000000 : ℝ), (660671959/2000000000 : ℝ), (4071194403/5000000000 : ℝ)] ![(161610408939/50000000000000 : ℝ), (4667346799461/20000000000000 : ℝ), (19085011294013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127129329/10000000000 : ℝ)|^67 ≤ (161610408939/50000000000000 : ℝ)^51
        have hw : |(-127129329/10000000000 : ℝ)|=(127129329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660671959/2000000000 : ℝ)|^67 ≤ (4667346799461/20000000000000 : ℝ)^51
        have hw : |(660671959/2000000000 : ℝ)|=(660671959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4071194403/5000000000 : ℝ)|^67 ≤ (19085011294013/25000000000000 : ℝ)^51
        have hw : |(4071194403/5000000000 : ℝ)|=(4071194403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1425848451/5000000000 : ℝ)*x 0 + (-466210021/5000000000 : ℝ)*x 1 + (8141794307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1425848451/5000000000 : ℝ)^67 ≤ (19237799739573/100000000000000 : ℝ)^51 := by
    have hnat : (1425848451 : ℕ)^67*100000000000000^51 ≤ 19237799739573^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425848451 5000000000 19237799739573 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466210021/5000000000 : ℝ)^67 ≤ (4429477439349/100000000000000 : ℝ)^51 := by
    have hnat : (466210021 : ℕ)^67*100000000000000^51 ≤ 4429477439349^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466210021 5000000000 4429477439349 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8141794307/10000000000 : ℝ)^67 ≤ (1192698793927/1562500000000 : ℝ)^51 := by
    have hnat : (8141794307 : ℕ)^67*1562500000000^51 ≤ 1192698793927^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8141794307 10000000000 1192698793927 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1425848451/5000000000 : ℝ), (-466210021/5000000000 : ℝ), (8141794307/10000000000 : ℝ)] ![(19237799739573/100000000000000 : ℝ), (4429477439349/100000000000000 : ℝ), (1192698793927/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1425848451/5000000000 : ℝ)|^67 ≤ (19237799739573/100000000000000 : ℝ)^51
        have hw : |(1425848451/5000000000 : ℝ)|=(1425848451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466210021/5000000000 : ℝ)|^67 ≤ (4429477439349/100000000000000 : ℝ)^51
        have hw : |(-466210021/5000000000 : ℝ)|=(466210021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8141794307/10000000000 : ℝ)|^67 ≤ (1192698793927/1562500000000 : ℝ)^51
        have hw : |(8141794307/10000000000 : ℝ)|=(8141794307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3976107813/5000000000 : ℝ)*x 0 + (3572211071/10000000000 : ℝ)*x 1 + (-31870841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3976107813/5000000000 : ℝ)^67 ≤ (37003154342259/50000000000000 : ℝ)^51 := by
    have hnat : (3976107813 : ℕ)^67*50000000000000^51 ≤ 37003154342259^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3976107813 5000000000 37003154342259 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3572211071/10000000000 : ℝ)^67 ≤ (25863189889683/100000000000000 : ℝ)^51 := by
    have hnat : (3572211071 : ℕ)^67*100000000000000^51 ≤ 25863189889683^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3572211071 10000000000 25863189889683 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31870841/5000000000 : ℝ)^67 ≤ (130501412303/100000000000000 : ℝ)^51 := by
    have hnat : (31870841 : ℕ)^67*100000000000000^51 ≤ 130501412303^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31870841 5000000000 130501412303 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3976107813/5000000000 : ℝ), (3572211071/10000000000 : ℝ), (-31870841/5000000000 : ℝ)] ![(37003154342259/50000000000000 : ℝ), (25863189889683/100000000000000 : ℝ), (130501412303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3976107813/5000000000 : ℝ)|^67 ≤ (37003154342259/50000000000000 : ℝ)^51
        have hw : |(3976107813/5000000000 : ℝ)|=(3976107813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3572211071/10000000000 : ℝ)|^67 ≤ (25863189889683/100000000000000 : ℝ)^51
        have hw : |(3572211071/10000000000 : ℝ)|=(3572211071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31870841/5000000000 : ℝ)|^67 ≤ (130501412303/100000000000000 : ℝ)^51
        have hw : |(-31870841/5000000000 : ℝ)|=(31870841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (59505999/78125000 : ℝ)*x 0 + (724517147/2500000000 : ℝ)*x 1 + (357571343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59505999/78125000 : ℝ)^67 ≤ (69932520535167/100000000000000 : ℝ)^51 := by
    have hnat : (59505999 : ℕ)^67*100000000000000^51 ≤ 69932520535167^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59505999 78125000 69932520535167 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724517147/2500000000 : ℝ)^67 ≤ (19649813609481/100000000000000 : ℝ)^51 := by
    have hnat : (724517147 : ℕ)^67*100000000000000^51 ≤ 19649813609481^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724517147 2500000000 19649813609481 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357571343/2000000000 : ℝ)^67 ≤ (104176658441/1000000000000 : ℝ)^51 := by
    have hnat : (357571343 : ℕ)^67*1000000000000^51 ≤ 104176658441^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357571343 2000000000 104176658441 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59505999/78125000 : ℝ), (724517147/2500000000 : ℝ), (357571343/2000000000 : ℝ)] ![(69932520535167/100000000000000 : ℝ), (19649813609481/100000000000000 : ℝ), (104176658441/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59505999/78125000 : ℝ)|^67 ≤ (69932520535167/100000000000000 : ℝ)^51
        have hw : |(59505999/78125000 : ℝ)|=(59505999/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(724517147/2500000000 : ℝ)|^67 ≤ (19649813609481/100000000000000 : ℝ)^51
        have hw : |(724517147/2500000000 : ℝ)|=(724517147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(357571343/2000000000 : ℝ)|^67 ≤ (104176658441/1000000000000 : ℝ)^51
        have hw : |(357571343/2000000000 : ℝ)|=(357571343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-71198303/5000000000 : ℝ)*x 0 + (7386046371/10000000000 : ℝ)*x 1 + (2123396639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71198303/5000000000 : ℝ)^67 ≤ (93787598499/25000000000000 : ℝ)^51 := by
    have hnat : (71198303 : ℕ)^67*25000000000000^51 ≤ 93787598499^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71198303 5000000000 93787598499 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7386046371/10000000000 : ℝ)^67 ≤ (16790728455871/25000000000000 : ℝ)^51 := by
    have hnat : (7386046371 : ℕ)^67*25000000000000^51 ≤ 16790728455871^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7386046371 10000000000 16790728455871 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123396639/5000000000 : ℝ)^67 ≤ (32461935777763/100000000000000 : ℝ)^51 := by
    have hnat : (2123396639 : ℕ)^67*100000000000000^51 ≤ 32461935777763^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123396639 5000000000 32461935777763 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71198303/5000000000 : ℝ), (7386046371/10000000000 : ℝ), (2123396639/5000000000 : ℝ)] ![(93787598499/25000000000000 : ℝ), (16790728455871/25000000000000 : ℝ), (32461935777763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71198303/5000000000 : ℝ)|^67 ≤ (93787598499/25000000000000 : ℝ)^51
        have hw : |(-71198303/5000000000 : ℝ)|=(71198303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7386046371/10000000000 : ℝ)|^67 ≤ (16790728455871/25000000000000 : ℝ)^51
        have hw : |(7386046371/10000000000 : ℝ)|=(7386046371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123396639/5000000000 : ℝ)|^67 ≤ (32461935777763/100000000000000 : ℝ)^51
        have hw : |(2123396639/5000000000 : ℝ)|=(2123396639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7895036467/10000000000 : ℝ)*x 0 + (-27116481/5000000000 : ℝ)*x 1 + (3647998321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7895036467/10000000000 : ℝ)^67 ≤ (36654012366923/50000000000000 : ℝ)^51 := by
    have hnat : (7895036467 : ℕ)^67*50000000000000^51 ≤ 36654012366923^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7895036467 10000000000 36654012366923 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27116481/5000000000 : ℝ)^67 ≤ (105546533809/100000000000000 : ℝ)^51 := by
    have hnat : (27116481 : ℕ)^67*100000000000000^51 ≤ 105546533809^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27116481 5000000000 105546533809 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3647998321/10000000000 : ℝ)^67 ≤ (26586428727407/100000000000000 : ℝ)^51 := by
    have hnat : (3647998321 : ℕ)^67*100000000000000^51 ≤ 26586428727407^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3647998321 10000000000 26586428727407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7895036467/10000000000 : ℝ), (-27116481/5000000000 : ℝ), (3647998321/10000000000 : ℝ)] ![(36654012366923/50000000000000 : ℝ), (105546533809/100000000000000 : ℝ), (26586428727407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7895036467/10000000000 : ℝ)|^67 ≤ (36654012366923/50000000000000 : ℝ)^51
        have hw : |(7895036467/10000000000 : ℝ)|=(7895036467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27116481/5000000000 : ℝ)|^67 ≤ (105546533809/100000000000000 : ℝ)^51
        have hw : |(-27116481/5000000000 : ℝ)|=(27116481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3647998321/10000000000 : ℝ)|^67 ≤ (26586428727407/100000000000000 : ℝ)^51
        have hw : |(3647998321/10000000000 : ℝ)|=(3647998321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2759863473/10000000000 : ℝ)*x 0 + (4127365423/5000000000 : ℝ)*x 1 + (-209308769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759863473/10000000000 : ℝ)^67 ≤ (18428067161697/100000000000000 : ℝ)^51 := by
    have hnat : (2759863473 : ℕ)^67*100000000000000^51 ≤ 18428067161697^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759863473 10000000000 18428067161697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127365423/5000000000 : ℝ)^67 ≤ (77726748248697/100000000000000 : ℝ)^51 := by
    have hnat : (4127365423 : ℕ)^67*100000000000000^51 ≤ 77726748248697^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127365423 5000000000 77726748248697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209308769/2500000000 : ℝ)^67 ≤ (3845184580051/100000000000000 : ℝ)^51 := by
    have hnat : (209308769 : ℕ)^67*100000000000000^51 ≤ 3845184580051^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209308769 2500000000 3845184580051 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759863473/10000000000 : ℝ), (4127365423/5000000000 : ℝ), (-209308769/2500000000 : ℝ)] ![(18428067161697/100000000000000 : ℝ), (77726748248697/100000000000000 : ℝ), (3845184580051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759863473/10000000000 : ℝ)|^67 ≤ (18428067161697/100000000000000 : ℝ)^51
        have hw : |(2759863473/10000000000 : ℝ)|=(2759863473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127365423/5000000000 : ℝ)|^67 ≤ (77726748248697/100000000000000 : ℝ)^51
        have hw : |(4127365423/5000000000 : ℝ)|=(4127365423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209308769/2500000000 : ℝ)|^67 ≤ (3845184580051/100000000000000 : ℝ)^51
        have hw : |(-209308769/2500000000 : ℝ)|=(209308769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s3_s3_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7749996563/10000000000 : ℝ)*x 0 + (2565744519/10000000000 : ℝ)*x 1 + (1954520901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7749996563/10000000000 : ℝ)^67 ≤ (35771946797677/50000000000000 : ℝ)^51 := by
    have hnat : (7749996563 : ℕ)^67*50000000000000^51 ≤ 35771946797677^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7749996563 10000000000 35771946797677 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565744519/10000000000 : ℝ)^67 ≤ (4186090429507/25000000000000 : ℝ)^51 := by
    have hnat : (2565744519 : ℕ)^67*25000000000000^51 ≤ 4186090429507^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565744519 10000000000 4186090429507 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954520901/10000000000 : ℝ)^67 ≤ (292793616657/2500000000000 : ℝ)^51 := by
    have hnat : (1954520901 : ℕ)^67*2500000000000^51 ≤ 292793616657^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954520901 10000000000 292793616657 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7749996563/10000000000 : ℝ), (2565744519/10000000000 : ℝ), (1954520901/10000000000 : ℝ)] ![(35771946797677/50000000000000 : ℝ), (4186090429507/25000000000000 : ℝ), (292793616657/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7749996563/10000000000 : ℝ)|^67 ≤ (35771946797677/50000000000000 : ℝ)^51
        have hw : |(7749996563/10000000000 : ℝ)|=(7749996563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565744519/10000000000 : ℝ)|^67 ≤ (4186090429507/25000000000000 : ℝ)^51
        have hw : |(2565744519/10000000000 : ℝ)|=(2565744519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1954520901/10000000000 : ℝ)|^67 ≤ (292793616657/2500000000000 : ℝ)^51
        have hw : |(1954520901/10000000000 : ℝ)|=(1954520901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((82347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79539/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79539/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74933/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72141/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (82347/100000 : ℝ) ^ (133/32 : ℝ) ≤ (44607829654127041251/100000000000000000000 : ℝ) := by
    have hpowers : (82347/100000 : ℝ)^133 ≤ (44607829654127041251/100000000000000000000 : ℝ)^32 := by
      have hnat : (82347 : ℕ)^133*100000000000000000000^32 ≤ 44607829654127041251^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82347 100000 44607829654127041251 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82347/100000 : ℝ)) (X := (44607829654127041251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (144607829654127041251/100000000000000000000 : ℝ) ≤ (2732010716614119/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (144607829654127041251/100000000000000000000 : ℝ)^32 ≤ (2732010716614119/2500000000000000 : ℝ)^133 := by
      have hnat : (144607829654127041251 : ℕ)^32*2500000000000000^133 ≤ 2732010716614119^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144607829654127041251 100000000000000000000 2732010716614119 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2732010716614119/2500000000000000 : ℝ)) (X := (144607829654127041251/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (94607829654127041251/50000000000000000000 : ℝ) ≤ (5829164255542371/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (94607829654127041251/50000000000000000000 : ℝ)^32 ≤ (5829164255542371/5000000000000000 : ℝ)^133 := by
      have hnat : (94607829654127041251 : ℕ)^32*5000000000000000^133 ≤ 5829164255542371^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94607829654127041251 50000000000000000000 5829164255542371 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5829164255542371/5000000000000000 : ℝ)) (X := (94607829654127041251/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(232010716614119/2058675000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(121714274104711/1372450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (82347/100000 : ℝ)) (alpha := (232010716614119/2058675000000000 : ℝ)) (beta := (121714274104711/1372450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (82347/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(232010716614119/2058675000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(121714274104711/1372450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (82379/100000 : ℝ) ^ (133/32 : ℝ) ≤ (22339960346183093807/50000000000000000000 : ℝ) := by
    have hpowers : (82379/100000 : ℝ)^133 ≤ (22339960346183093807/50000000000000000000 : ℝ)^32 := by
      have hnat : (82379 : ℕ)^133*50000000000000000000^32 ≤ 22339960346183093807^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82379 100000 22339960346183093807 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82379/100000 : ℝ)) (X := (22339960346183093807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (72339960346183093807/50000000000000000000 : ℝ) ≤ (10929353399596877/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (72339960346183093807/50000000000000000000 : ℝ)^32 ≤ (10929353399596877/10000000000000000 : ℝ)^133 := by
      have hnat : (72339960346183093807 : ℕ)^32*10000000000000000^133 ≤ 10929353399596877^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72339960346183093807 50000000000000000000 10929353399596877 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10929353399596877/10000000000000000 : ℝ)) (X := (72339960346183093807/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (47339960346183093807/25000000000000000000 : ℝ) ≤ (1166046530781303/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (47339960346183093807/25000000000000000000 : ℝ)^32 ≤ (1166046530781303/1000000000000000 : ℝ)^133 := by
      have hnat : (47339960346183093807 : ℕ)^32*1000000000000000^133 ≤ 1166046530781303^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47339960346183093807 25000000000000000000 1166046530781303 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1166046530781303/1000000000000000 : ℝ)) (X := (47339960346183093807/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(929353399596877/8237900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(731111908216153/8237900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (82379/100000 : ℝ)) (alpha := (929353399596877/8237900000000000 : ℝ)) (beta := (731111908216153/8237900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (82379/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(929353399596877/8237900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(731111908216153/8237900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (79539/100000 : ℝ) ^ (133/32 : ℝ) ≤ (19308838729528394539/50000000000000000000 : ℝ) := by
    have hpowers : (79539/100000 : ℝ)^133 ≤ (19308838729528394539/50000000000000000000 : ℝ)^32 := by
      have hnat : (79539 : ℕ)^133*50000000000000000000^32 ≤ 19308838729528394539^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79539 100000 19308838729528394539 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79539/100000 : ℝ)) (X := (19308838729528394539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (69308838729528394539/50000000000000000000 : ℝ) ≤ (10817372193521751/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (69308838729528394539/50000000000000000000 : ℝ)^32 ≤ (10817372193521751/10000000000000000 : ℝ)^133 := by
      have hnat : (69308838729528394539 : ℕ)^32*10000000000000000^133 ≤ 10817372193521751^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69308838729528394539 50000000000000000000 10817372193521751 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10817372193521751/10000000000000000 : ℝ)) (X := (69308838729528394539/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (44308838729528394539/25000000000000000000 : ℝ) ≤ (11476292010681519/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (44308838729528394539/25000000000000000000 : ℝ)^32 ≤ (11476292010681519/10000000000000000 : ℝ)^133 := by
      have hnat : (44308838729528394539 : ℕ)^32*10000000000000000^133 ≤ 11476292010681519^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44308838729528394539 25000000000000000000 11476292010681519 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11476292010681519/10000000000000000 : ℝ)) (X := (44308838729528394539/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(817372193521751/7953900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(27454992381657/331412500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (79539/100000 : ℝ)) (alpha := (817372193521751/7953900000000000 : ℝ)) (beta := (27454992381657/331412500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79539/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(817372193521751/7953900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(27454992381657/331412500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-128333351/2000000000 : ℝ)*X 0 0+(2827268297/5000000000 : ℝ)*X 0 1+(5900492111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5654576803/10000000000 : ℝ)*X 1 0+(-642524647/10000000000 : ℝ)*X 1 1+(2950012323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1431476319/2500000000 : ℝ)*X 2 0+(5866425529/10000000000 : ℝ)*X 2 1+(-141750469/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((2339748319/5000000000 : ℝ)*X 0 0+(4374929829/10000000000 : ℝ)*X 0 1+(3935270519/10000000000 : ℝ)*X 0 2+(2339748319/5000000000 : ℝ)*X 1 0+(4374929829/10000000000 : ℝ)*X 1 1+(3935270519/10000000000 : ℝ)*X 1 2+(2339748319/5000000000 : ℝ)*X 2 0+(4374929829/10000000000 : ℝ)*X 2 1+(3935270519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-939768723/10000000000 : ℝ)*X 0 0+(1476964337/5000000000 : ℝ)*X 0 1+(8063977951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((423981011/1250000000 : ℝ)*X 1 0+(-169067873/10000000000 : ℝ)*X 1 1+(2015847931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((412700343/1250000000 : ℝ)*X 2 0+(8164554431/10000000000 : ℝ)*X 2 1+(-38109399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((3383909279/10000000000 : ℝ)*X 0 0+(1809426011/2500000000 : ℝ)*X 0 1+(1800743659/10000000000 : ℝ)*X 0 2+(3383909279/10000000000 : ℝ)*X 1 0+(1809426011/2500000000 : ℝ)*X 1 1+(1800743659/10000000000 : ℝ)*X 1 2+(3383909279/10000000000 : ℝ)*X 2 0+(1809426011/2500000000 : ℝ)*X 2 1+(1800743659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-127129329/10000000000 : ℝ)*X 0 0+(660671959/2000000000 : ℝ)*X 0 1+(4071194403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1425848451/5000000000 : ℝ)*X 1 0+(-466210021/5000000000 : ℝ)*X 1 1+(8141794307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((3976107813/5000000000 : ℝ)*X 2 0+(3572211071/10000000000 : ℝ)*X 2 1+(-31870841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((59505999/78125000 : ℝ)*X 0 0+(724517147/2500000000 : ℝ)*X 0 1+(357571343/2000000000 : ℝ)*X 0 2+(59505999/78125000 : ℝ)*X 1 0+(724517147/2500000000 : ℝ)*X 1 1+(357571343/2000000000 : ℝ)*X 1 2+(59505999/78125000 : ℝ)*X 2 0+(724517147/2500000000 : ℝ)*X 2 1+(357571343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-71198303/5000000000 : ℝ)*X 0 0+(7386046371/10000000000 : ℝ)*X 0 1+(2123396639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((7895036467/10000000000 : ℝ)*X 1 0+(-27116481/5000000000 : ℝ)*X 1 1+(3647998321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2759863473/10000000000 : ℝ)*X 2 0+(4127365423/5000000000 : ℝ)*X 2 1+(-209308769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7749996563/10000000000 : ℝ)*X 0 0+(2565744519/10000000000 : ℝ)*X 0 1+(1954520901/10000000000 : ℝ)*X 0 2+(7749996563/10000000000 : ℝ)*X 1 0+(2565744519/10000000000 : ℝ)*X 1 1+(1954520901/10000000000 : ℝ)*X 1 2+(7749996563/10000000000 : ℝ)*X 2 0+(2565744519/10000000000 : ℝ)*X 2 1+(1954520901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((37309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41243789817737343172035508760937/2997587845336150000000000000000000000 : ℝ) := by norm_num
    linear_combination (165678535779/250000000000 : ℝ)*(base7) + (1637797/1000000000000 : ℝ)*(base50) + (37689017647/1000000000000 : ℝ)*(base60) + (932791746561/500000000000 : ℝ)*(major_s3_0) + (932791746561/500000000000 : ℝ)*(major_s3_1) + (932791746561/500000000000 : ℝ)*(major_s3_2) + (5663933/500000000000 : ℝ)*(sp_s3_0) + (1723857/1000000000000 : ℝ)*(sp_s3_6) + (1049150402227/500000000000 : ℝ)*(sp_s3_7) + (2098395049219/1000000000000 : ℝ)*(sp_s3_8) + (1049197525123/500000000000 : ℝ)*(sp_s3_9) + (1882622110827/1000000000000 : ℝ)*(sp_s3_13) + (82916899/1000000000000 : ℝ)*(sp_s3_14) + (1219909691569/1000000000000 : ℝ)*(f.failure) + (2098395049219/1000000000000 : ℝ)*(f.sum) + (9444503364160027631/27301430337500000000000000000000 : ℝ)*base63 + (466934347683063/662825000000000000000000000 : ℝ)*base65 + (811772309621083/4118950000000000000000000000 : ℝ)*base67 + (225072299503411/662825000000000000000000000 : ℝ)*base69 + (60185531233657707/145551067400000000000000000000 : ℝ)*base71 + (369214372568701/686225000000000000000000000 : ℝ)*base73 + (145590703054759511/514868750000000000000000000 : ℝ)*base74 + (1162409787097828403/1372450000000000000000000000 : ℝ)*base76 + (387680389916752763497/4522442342000000000000000000000 : ℝ)*base79 + (1027/1000000000000 : ℝ)*base85 + (2001/3125000000000000 : ℝ)*base87 + (2001/3125000000000000 : ℝ)*base89 + (2001/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74933/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (128368763284701483270838363/7277553370000000000000000000000 : ℝ) := by norm_num
    linear_combination (679619596299/1000000000000 : ℝ)*(base7) + (125871/200000000000 : ℝ)*(base49) + (999029/1000000000000 : ℝ)*(base53) + (449337212907/250000000000 : ℝ)*(major_s3_0) + (449337212907/250000000000 : ℝ)*(major_s3_1) + (1797347852599/1000000000000 : ℝ)*(major_s3_2) + (1785021/1000000000000 : ℝ)*(sp_s3_0) + (1208671/1000000000000 : ℝ)*(sp_s3_7) + (3743919/40000000000 : ℝ)*(sp_s3_8) + (499001881293/250000000000 : ℝ)*(sp_s3_14) + (249489615111/125000000000 : ℝ)*(sp_s3_15) + (1996011517893/1000000000000 : ℝ)*(sp_s3_16) + (927382033129/500000000000 : ℝ)*(sp_s3_20) + (36604907/250000000000 : ℝ)*(sp_s3_27) + (293822722397/250000000000 : ℝ)*(f.failure) + (1996011517893/1000000000000 : ℝ)*(f.sum) + (6491293224611465953/11913351420000000000000000000000 : ℝ)*base63 + (179303470131397/331412500000000000000000000 : ℝ)*base64 + (12354315365917/93612500000000000000000000 : ℝ)*base66 + (2073080777357609/7953900000000000000000000000 : ℝ)*base69 + (4051941478374790547/36387766850000000000000000000000 : ℝ)*base71 + (138451442326039/686225000000000000000000000 : ℝ)*base73 + (16430558603853/93612500000000000000000000 : ℝ)*base74 + (606078745482067/1372450000000000000000000000 : ℝ)*base76 + (477743155658464603/1027827805000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (111/97656250000000 : ℝ)*base87 + (111/97656250000000 : ℝ)*base89 + (111/97656250000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72141/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6060846674016939726515419271973/599517569067230000000000000000000000 : ℝ) := by norm_num
    linear_combination (674148448837/1000000000000 : ℝ)*(base7) + (652483/500000000000 : ℝ)*(base11) + (22891681763/200000000000 : ℝ)*(base40) + (465429/1000000000000 : ℝ)*(base49) + (346695506607/200000000000 : ℝ)*(major_s3_0) + (346695506607/200000000000 : ℝ)*(major_s3_1) + (346695506607/200000000000 : ℝ)*(major_s3_2) + (2849581/250000000000 : ℝ)*(sp_s3_1) + (11348643/1000000000000 : ℝ)*(sp_s3_2) + (36869479/500000000000 : ℝ)*(sp_s3_9) + (956722057639/500000000000 : ℝ)*(sp_s3_21) + (11958962637/6250000000 : ℝ)*(sp_s3_22) + (478340083161/250000000000 : ℝ)*(sp_s3_23) + (1807673724153/1000000000000 : ℝ)*(sp_s3_27) + (283381318829/250000000000 : ℝ)*(f.failure) + (382689084049/200000000000 : ℝ)*(f.sum) + (4993038191478888763/21841144270000000000000000000000 : ℝ)*base62 + (30401694582611/265130000000000000000000000 : ℝ)*base65 + (45980688295319/65903200000000000000000000 : ℝ)*base66 + (56736214778107/530260000000000000000000000 : ℝ)*base68 + (1426385349060308647/7277553370000000000000000000000 : ℝ)*base71 + (33009420601649/68622500000000000000000000 : ℝ)*base72 + (1022112729875679/1647580000000000000000000000 : ℝ)*base74 + (60105090209551/137245000000000000000000000 : ℝ)*base76 + (37014114093666253013/45224423420000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (789/3125000000000000 : ℝ)*base87 + (789/3125000000000000 : ℝ)*base89 + (789/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((82347/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82347/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82379/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79539/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79539/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74933/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(74933/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(72141/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(72141/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s3 p hpa hpb X hX hprev2

#print axioms solution
