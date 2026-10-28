-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304052_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:00.47413+00:00
-- url     : https://prove2.me/submissions/4b5de65b-c68b-438d-84b8-d4a2b7e856a9

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
theorem collision_support_c304052_s1_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-35471501/250000000 : ℝ)*x 0 + (667451213/2000000000 : ℝ)*x 1 + (-7480291307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35471501/250000000 : ℝ)^17 ≤ (7780327585903/100000000000000 : ℝ)^13 := by
    have hnat : (35471501 : ℕ)^17*100000000000000^13 ≤ 7780327585903^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35471501 250000000 7780327585903 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667451213/2000000000 : ℝ)^17 ≤ (23808945227627/100000000000000 : ℝ)^13 := by
    have hnat : (667451213 : ℕ)^17*100000000000000^13 ≤ 23808945227627^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667451213 2000000000 23808945227627 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7480291307/10000000000 : ℝ)^17 ≤ (34205363583031/50000000000000 : ℝ)^13 := by
    have hnat : (7480291307 : ℕ)^17*50000000000000^13 ≤ 34205363583031^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7480291307 10000000000 34205363583031 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35471501/250000000 : ℝ), (667451213/2000000000 : ℝ), (-7480291307/10000000000 : ℝ)] ![(7780327585903/100000000000000 : ℝ), (23808945227627/100000000000000 : ℝ), (34205363583031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35471501/250000000 : ℝ)|^17 ≤ (7780327585903/100000000000000 : ℝ)^13
        have hw : |(-35471501/250000000 : ℝ)|=(35471501/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667451213/2000000000 : ℝ)|^17 ≤ (23808945227627/100000000000000 : ℝ)^13
        have hw : |(667451213/2000000000 : ℝ)|=(667451213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7480291307/10000000000 : ℝ)|^17 ≤ (34205363583031/50000000000000 : ℝ)^13
        have hw : |(-7480291307/10000000000 : ℝ)|=(7480291307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1183869023/2500000000 : ℝ)*x 0 + (-286641029/1000000000 : ℝ)*x 1 + (-5231543339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1183869023/2500000000 : ℝ)^17 ≤ (37624916096307/100000000000000 : ℝ)^13 := by
    have hnat : (1183869023 : ℕ)^17*100000000000000^13 ≤ 37624916096307^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183869023 2500000000 37624916096307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286641029/1000000000 : ℝ)^17 ≤ (9757432249807/50000000000000 : ℝ)^13 := by
    have hnat : (286641029 : ℕ)^17*50000000000000^13 ≤ 9757432249807^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286641029 1000000000 9757432249807 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231543339/10000000000 : ℝ)^17 ≤ (10715054847019/25000000000000 : ℝ)^13 := by
    have hnat : (5231543339 : ℕ)^17*25000000000000^13 ≤ 10715054847019^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231543339 10000000000 10715054847019 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1183869023/2500000000 : ℝ), (-286641029/1000000000 : ℝ), (-5231543339/10000000000 : ℝ)] ![(37624916096307/100000000000000 : ℝ), (9757432249807/50000000000000 : ℝ), (10715054847019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1183869023/2500000000 : ℝ)|^17 ≤ (37624916096307/100000000000000 : ℝ)^13
        have hw : |(1183869023/2500000000 : ℝ)|=(1183869023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286641029/1000000000 : ℝ)|^17 ≤ (9757432249807/50000000000000 : ℝ)^13
        have hw : |(-286641029/1000000000 : ℝ)|=(286641029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5231543339/10000000000 : ℝ)|^17 ≤ (10715054847019/25000000000000 : ℝ)^13
        have hw : |(-5231543339/10000000000 : ℝ)|=(5231543339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5045411811/10000000000 : ℝ)*x 0 + (3067209941/5000000000 : ℝ)*x 1 + (606804339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5045411811/10000000000 : ℝ)^17 ≤ (40877111039379/100000000000000 : ℝ)^13 := by
    have hnat : (5045411811 : ℕ)^17*100000000000000^13 ≤ 40877111039379^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045411811 10000000000 40877111039379 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3067209941/5000000000 : ℝ)^17 ≤ (52780443706237/100000000000000 : ℝ)^13 := by
    have hnat : (3067209941 : ℕ)^17*100000000000000^13 ≤ 52780443706237^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3067209941 5000000000 52780443706237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606804339/5000000000 : ℝ)^17 ≤ (1585611311073/25000000000000 : ℝ)^13 := by
    have hnat : (606804339 : ℕ)^17*25000000000000^13 ≤ 1585611311073^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606804339 5000000000 1585611311073 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5045411811/10000000000 : ℝ), (3067209941/5000000000 : ℝ), (606804339/5000000000 : ℝ)] ![(40877111039379/100000000000000 : ℝ), (52780443706237/100000000000000 : ℝ), (1585611311073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5045411811/10000000000 : ℝ)|^17 ≤ (40877111039379/100000000000000 : ℝ)^13
        have hw : |(5045411811/10000000000 : ℝ)|=(5045411811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3067209941/5000000000 : ℝ)|^17 ≤ (52780443706237/100000000000000 : ℝ)^13
        have hw : |(3067209941/5000000000 : ℝ)|=(3067209941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606804339/5000000000 : ℝ)|^17 ≤ (1585611311073/25000000000000 : ℝ)^13
        have hw : |(606804339/5000000000 : ℝ)|=(606804339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008021519/10000000000 : ℝ)*x 0 + (1742614293/10000000000 : ℝ)*x 1 + (-8819010437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008021519/10000000000 : ℝ)^17 ≤ (4975596200999/100000000000000 : ℝ)^13 := by
    have hnat : (1008021519 : ℕ)^17*100000000000000^13 ≤ 4975596200999^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008021519 10000000000 4975596200999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1742614293/10000000000 : ℝ)^17 ≤ (2544864999463/25000000000000 : ℝ)^13 := by
    have hnat : (1742614293 : ℕ)^17*25000000000000^13 ≤ 2544864999463^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742614293 10000000000 2544864999463 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8819010437/10000000000 : ℝ)^17 ≤ (84844943791921/100000000000000 : ℝ)^13 := by
    have hnat : (8819010437 : ℕ)^17*100000000000000^13 ≤ 84844943791921^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8819010437 10000000000 84844943791921 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008021519/10000000000 : ℝ), (1742614293/10000000000 : ℝ), (-8819010437/10000000000 : ℝ)] ![(4975596200999/100000000000000 : ℝ), (2544864999463/25000000000000 : ℝ), (84844943791921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008021519/10000000000 : ℝ)|^17 ≤ (4975596200999/100000000000000 : ℝ)^13
        have hw : |(-1008021519/10000000000 : ℝ)|=(1008021519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1742614293/10000000000 : ℝ)|^17 ≤ (2544864999463/25000000000000 : ℝ)^13
        have hw : |(1742614293/10000000000 : ℝ)|=(1742614293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8819010437/10000000000 : ℝ)|^17 ≤ (84844943791921/100000000000000 : ℝ)^13
        have hw : |(-8819010437/10000000000 : ℝ)|=(8819010437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1713721479/5000000000 : ℝ)*x 0 + (-1960611923/10000000000 : ℝ)*x 1 + (-3531787263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713721479/5000000000 : ℝ)^17 ≤ (12326908112961/50000000000000 : ℝ)^13 := by
    have hnat : (1713721479 : ℕ)^17*50000000000000^13 ≤ 12326908112961^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713721479 5000000000 12326908112961 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960611923/10000000000 : ℝ)^17 ≤ (11875885177371/100000000000000 : ℝ)^13 := by
    have hnat : (1960611923 : ℕ)^17*100000000000000^13 ≤ 11875885177371^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960611923 10000000000 11875885177371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3531787263/5000000000 : ℝ)^17 ≤ (1983446830839/3125000000000 : ℝ)^13 := by
    have hnat : (3531787263 : ℕ)^17*3125000000000^13 ≤ 1983446830839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3531787263 5000000000 1983446830839 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1713721479/5000000000 : ℝ), (-1960611923/10000000000 : ℝ), (-3531787263/5000000000 : ℝ)] ![(12326908112961/50000000000000 : ℝ), (11875885177371/100000000000000 : ℝ), (1983446830839/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1713721479/5000000000 : ℝ)|^17 ≤ (12326908112961/50000000000000 : ℝ)^13
        have hw : |(1713721479/5000000000 : ℝ)|=(1713721479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960611923/10000000000 : ℝ)|^17 ≤ (11875885177371/100000000000000 : ℝ)^13
        have hw : |(-1960611923/10000000000 : ℝ)|=(1960611923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3531787263/5000000000 : ℝ)|^17 ≤ (1983446830839/3125000000000 : ℝ)^13
        have hw : |(-3531787263/5000000000 : ℝ)|=(3531787263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1887535861/5000000000 : ℝ)*x 0 + (1935518203/2500000000 : ℝ)*x 1 + (41352047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887535861/5000000000 : ℝ)^17 ≤ (874174974371/3125000000000 : ℝ)^13 := by
    have hnat : (1887535861 : ℕ)^17*3125000000000^13 ≤ 874174974371^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887535861 5000000000 874174974371 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935518203/2500000000 : ℝ)^17 ≤ (71558212355519/100000000000000 : ℝ)^13 := by
    have hnat : (1935518203 : ℕ)^17*100000000000000^13 ≤ 71558212355519^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935518203 2500000000 71558212355519 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41352047/2500000000 : ℝ)^17 ≤ (93637690437/20000000000000 : ℝ)^13 := by
    have hnat : (41352047 : ℕ)^17*20000000000000^13 ≤ 93637690437^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41352047 2500000000 93637690437 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1887535861/5000000000 : ℝ), (1935518203/2500000000 : ℝ), (41352047/2500000000 : ℝ)] ![(874174974371/3125000000000 : ℝ), (71558212355519/100000000000000 : ℝ), (93637690437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1887535861/5000000000 : ℝ)|^17 ≤ (874174974371/3125000000000 : ℝ)^13
        have hw : |(1887535861/5000000000 : ℝ)|=(1887535861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1935518203/2500000000 : ℝ)|^17 ≤ (71558212355519/100000000000000 : ℝ)^13
        have hw : |(1935518203/2500000000 : ℝ)|=(1935518203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41352047/2500000000 : ℝ)|^17 ≤ (93637690437/20000000000000 : ℝ)^13
        have hw : |(41352047/2500000000 : ℝ)|=(41352047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1136279713/2500000000 : ℝ)*x 0 + (3541160927/5000000000 : ℝ)*x 1 + (-106274999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136279713/2500000000 : ℝ)^17 ≤ (3565944258401/10000000000000 : ℝ)^13 := by
    have hnat : (1136279713 : ℕ)^17*10000000000000^13 ≤ 3565944258401^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136279713 2500000000 3565944258401 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3541160927/5000000000 : ℝ)^17 ≤ (6369067653917/10000000000000 : ℝ)^13 := by
    have hnat : (3541160927 : ℕ)^17*10000000000000^13 ≤ 6369067653917^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541160927 5000000000 6369067653917 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106274999/5000000000 : ℝ)^17 ≤ (649880869677/100000000000000 : ℝ)^13 := by
    have hnat : (106274999 : ℕ)^17*100000000000000^13 ≤ 649880869677^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106274999 5000000000 649880869677 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1136279713/2500000000 : ℝ), (3541160927/5000000000 : ℝ), (-106274999/5000000000 : ℝ)] ![(3565944258401/10000000000000 : ℝ), (6369067653917/10000000000000 : ℝ), (649880869677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1136279713/2500000000 : ℝ)|^17 ≤ (3565944258401/10000000000000 : ℝ)^13
        have hw : |(1136279713/2500000000 : ℝ)|=(1136279713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3541160927/5000000000 : ℝ)|^17 ≤ (6369067653917/10000000000000 : ℝ)^13
        have hw : |(3541160927/5000000000 : ℝ)|=(3541160927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106274999/5000000000 : ℝ)|^17 ≤ (649880869677/100000000000000 : ℝ)^13
        have hw : |(-106274999/5000000000 : ℝ)|=(106274999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-210711707/10000000000 : ℝ)*x 0 + (1913708317/10000000000 : ℝ)*x 1 + (-905702381/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210711707/10000000000 : ℝ)^17 ≤ (80317572769/12500000000000 : ℝ)^13 := by
    have hnat : (210711707 : ℕ)^17*12500000000000^13 ≤ 80317572769^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210711707 10000000000 80317572769 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913708317/10000000000 : ℝ)^17 ≤ (179777137419/1562500000000 : ℝ)^13 := by
    have hnat : (1913708317 : ℕ)^17*1562500000000^13 ≤ 179777137419^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913708317 10000000000 179777137419 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905702381/1000000000 : ℝ)^17 ≤ (43925861302461/50000000000000 : ℝ)^13 := by
    have hnat : (905702381 : ℕ)^17*50000000000000^13 ≤ 43925861302461^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905702381 1000000000 43925861302461 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-210711707/10000000000 : ℝ), (1913708317/10000000000 : ℝ), (-905702381/1000000000 : ℝ)] ![(80317572769/12500000000000 : ℝ), (179777137419/1562500000000 : ℝ), (43925861302461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-210711707/10000000000 : ℝ)|^17 ≤ (80317572769/12500000000000 : ℝ)^13
        have hw : |(-210711707/10000000000 : ℝ)|=(210711707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913708317/10000000000 : ℝ)|^17 ≤ (179777137419/1562500000000 : ℝ)^13
        have hw : |(1913708317/10000000000 : ℝ)|=(1913708317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905702381/1000000000 : ℝ)|^17 ≤ (43925861302461/50000000000000 : ℝ)^13
        have hw : |(-905702381/1000000000 : ℝ)|=(905702381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3021926113/10000000000 : ℝ)*x 0 + (-558351721/2500000000 : ℝ)*x 1 + (-1798509509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3021926113/10000000000 : ℝ)^17 ≤ (1306926592187/6250000000000 : ℝ)^13 := by
    have hnat : (3021926113 : ℕ)^17*6250000000000^13 ≤ 1306926592187^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021926113 10000000000 1306926592187 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558351721/2500000000 : ℝ)^17 ≤ (7040771828253/50000000000000 : ℝ)^13 := by
    have hnat : (558351721 : ℕ)^17*50000000000000^13 ≤ 7040771828253^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558351721 2500000000 7040771828253 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1798509509/2500000000 : ℝ)^17 ≤ (16251907711769/25000000000000 : ℝ)^13 := by
    have hnat : (1798509509 : ℕ)^17*25000000000000^13 ≤ 16251907711769^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798509509 2500000000 16251907711769 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3021926113/10000000000 : ℝ), (-558351721/2500000000 : ℝ), (-1798509509/2500000000 : ℝ)] ![(1306926592187/6250000000000 : ℝ), (7040771828253/50000000000000 : ℝ), (16251907711769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3021926113/10000000000 : ℝ)|^17 ≤ (1306926592187/6250000000000 : ℝ)^13
        have hw : |(3021926113/10000000000 : ℝ)|=(3021926113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558351721/2500000000 : ℝ)|^17 ≤ (7040771828253/50000000000000 : ℝ)^13
        have hw : |(-558351721/2500000000 : ℝ)|=(558351721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1798509509/2500000000 : ℝ)|^17 ≤ (16251907711769/25000000000000 : ℝ)^13
        have hw : |(-1798509509/2500000000 : ℝ)|=(1798509509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7312018291/10000000000 : ℝ)*x 0 + (105960833/250000000 : ℝ)*x 1 + (306441813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7312018291/10000000000 : ℝ)^17 ≤ (2075164858719/3125000000000 : ℝ)^13 := by
    have hnat : (7312018291 : ℕ)^17*3125000000000^13 ≤ 2075164858719^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7312018291 10000000000 2075164858719 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105960833/250000000 : ℝ)^17 ≤ (4068265835287/12500000000000 : ℝ)^13 := by
    have hnat : (105960833 : ℕ)^17*12500000000000^13 ≤ 4068265835287^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105960833 250000000 4068265835287 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306441813/10000000000 : ℝ)^17 ≤ (524298913351/50000000000000 : ℝ)^13 := by
    have hnat : (306441813 : ℕ)^17*50000000000000^13 ≤ 524298913351^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306441813 10000000000 524298913351 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7312018291/10000000000 : ℝ), (105960833/250000000 : ℝ), (306441813/10000000000 : ℝ)] ![(2075164858719/3125000000000 : ℝ), (4068265835287/12500000000000 : ℝ), (524298913351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7312018291/10000000000 : ℝ)|^17 ≤ (2075164858719/3125000000000 : ℝ)^13
        have hw : |(7312018291/10000000000 : ℝ)|=(7312018291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105960833/250000000 : ℝ)|^17 ≤ (4068265835287/12500000000000 : ℝ)^13
        have hw : |(105960833/250000000 : ℝ)|=(105960833/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(306441813/10000000000 : ℝ)|^17 ≤ (524298913351/50000000000000 : ℝ)^13
        have hw : |(306441813/10000000000 : ℝ)|=(306441813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4140805861/5000000000 : ℝ)*x 0 + (3003715027/10000000000 : ℝ)*x 1 + (-319084921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4140805861/5000000000 : ℝ)^17 ≤ (1221066917179/1562500000000 : ℝ)^13 := by
    have hnat : (4140805861 : ℕ)^17*1562500000000^13 ≤ 1221066917179^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140805861 5000000000 1221066917179 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3003715027/10000000000 : ℝ)^17 ≤ (20746189266489/100000000000000 : ℝ)^13 := by
    have hnat : (3003715027 : ℕ)^17*100000000000000^13 ≤ 20746189266489^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003715027 10000000000 20746189266489 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319084921/10000000000 : ℝ)^17 ≤ (110552801481/10000000000000 : ℝ)^13 := by
    have hnat : (319084921 : ℕ)^17*10000000000000^13 ≤ 110552801481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319084921 10000000000 110552801481 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4140805861/5000000000 : ℝ), (3003715027/10000000000 : ℝ), (-319084921/10000000000 : ℝ)] ![(1221066917179/1562500000000 : ℝ), (20746189266489/100000000000000 : ℝ), (110552801481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4140805861/5000000000 : ℝ)|^17 ≤ (1221066917179/1562500000000 : ℝ)^13
        have hw : |(4140805861/5000000000 : ℝ)|=(4140805861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3003715027/10000000000 : ℝ)|^17 ≤ (20746189266489/100000000000000 : ℝ)^13
        have hw : |(3003715027/10000000000 : ℝ)|=(3003715027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319084921/10000000000 : ℝ)|^17 ≤ (110552801481/10000000000000 : ℝ)^13
        have hw : |(-319084921/10000000000 : ℝ)|=(319084921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-19221/10000000000 : ℝ)*x 0 + (4602348269/10000000000 : ℝ)*x 1 + (-7087558221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19221/10000000000 : ℝ)^17 ≤ (133967/4000000000000 : ℝ)^13 := by
    have hnat : (19221 : ℕ)^17*4000000000000^13 ≤ 133967^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19221 10000000000 133967 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4602348269/10000000000 : ℝ)^17 ≤ (36247733638627/100000000000000 : ℝ)^13 := by
    have hnat : (4602348269 : ℕ)^17*100000000000000^13 ≤ 36247733638627^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602348269 10000000000 36247733638627 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7087558221/10000000000 : ℝ)^17 ≤ (63752262998639/100000000000000 : ℝ)^13 := by
    have hnat : (7087558221 : ℕ)^17*100000000000000^13 ≤ 63752262998639^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7087558221 10000000000 63752262998639 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19221/10000000000 : ℝ), (4602348269/10000000000 : ℝ), (-7087558221/10000000000 : ℝ)] ![(133967/4000000000000 : ℝ), (36247733638627/100000000000000 : ℝ), (63752262998639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19221/10000000000 : ℝ)|^17 ≤ (133967/4000000000000 : ℝ)^13
        have hw : |(-19221/10000000000 : ℝ)|=(19221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4602348269/10000000000 : ℝ)|^17 ≤ (36247733638627/100000000000000 : ℝ)^13
        have hw : |(4602348269/10000000000 : ℝ)|=(4602348269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7087558221/10000000000 : ℝ)|^17 ≤ (63752262998639/100000000000000 : ℝ)^13
        have hw : |(-7087558221/10000000000 : ℝ)|=(7087558221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6809627963/10000000000 : ℝ)*x 0 + (-282735219/1250000000 : ℝ)*x 1 + (-1741634669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6809627963/10000000000 : ℝ)^17 ≤ (60502975659183/100000000000000 : ℝ)^13 := by
    have hnat : (6809627963 : ℕ)^17*100000000000000^13 ≤ 60502975659183^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6809627963 10000000000 60502975659183 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282735219/1250000000 : ℝ)^17 ≤ (14316776649871/100000000000000 : ℝ)^13 := by
    have hnat : (282735219 : ℕ)^17*100000000000000^13 ≤ 14316776649871^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282735219 1250000000 14316776649871 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741634669/5000000000 : ℝ)^17 ≤ (25180247667767/100000000000000 : ℝ)^13 := by
    have hnat : (1741634669 : ℕ)^17*100000000000000^13 ≤ 25180247667767^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741634669 5000000000 25180247667767 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6809627963/10000000000 : ℝ), (-282735219/1250000000 : ℝ), (-1741634669/5000000000 : ℝ)] ![(60502975659183/100000000000000 : ℝ), (14316776649871/100000000000000 : ℝ), (25180247667767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6809627963/10000000000 : ℝ)|^17 ≤ (60502975659183/100000000000000 : ℝ)^13
        have hw : |(6809627963/10000000000 : ℝ)|=(6809627963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282735219/1250000000 : ℝ)|^17 ≤ (14316776649871/100000000000000 : ℝ)^13
        have hw : |(-282735219/1250000000 : ℝ)|=(282735219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1741634669/5000000000 : ℝ)|^17 ≤ (25180247667767/100000000000000 : ℝ)^13
        have hw : |(-1741634669/5000000000 : ℝ)|=(1741634669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (917808081/2500000000 : ℝ)*x 0 + (7467829289/10000000000 : ℝ)*x 1 + (975480763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (917808081/2500000000 : ℝ)^17 ≤ (26971669419459/100000000000000 : ℝ)^13 := by
    have hnat : (917808081 : ℕ)^17*100000000000000^13 ≤ 26971669419459^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917808081 2500000000 26971669419459 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7467829289/10000000000 : ℝ)^17 ≤ (68261726479283/100000000000000 : ℝ)^13 := by
    have hnat : (7467829289 : ℕ)^17*100000000000000^13 ≤ 68261726479283^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7467829289 10000000000 68261726479283 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975480763/10000000000 : ℝ)^17 ≤ (4766604090941/100000000000000 : ℝ)^13 := by
    have hnat : (975480763 : ℕ)^17*100000000000000^13 ≤ 4766604090941^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975480763 10000000000 4766604090941 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(917808081/2500000000 : ℝ), (7467829289/10000000000 : ℝ), (975480763/10000000000 : ℝ)] ![(26971669419459/100000000000000 : ℝ), (68261726479283/100000000000000 : ℝ), (4766604090941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(917808081/2500000000 : ℝ)|^17 ≤ (26971669419459/100000000000000 : ℝ)^13
        have hw : |(917808081/2500000000 : ℝ)|=(917808081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7467829289/10000000000 : ℝ)|^17 ≤ (68261726479283/100000000000000 : ℝ)^13
        have hw : |(7467829289/10000000000 : ℝ)|=(7467829289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(975480763/10000000000 : ℝ)|^17 ≤ (4766604090941/100000000000000 : ℝ)^13
        have hw : |(975480763/10000000000 : ℝ)|=(975480763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s1_s1_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (858784419/1000000000 : ℝ)*x 0 + (2564692669/10000000000 : ℝ)*x 1 + (-2617277/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858784419/1000000000 : ℝ)^17 ≤ (81948464398013/100000000000000 : ℝ)^13 := by
    have hnat : (858784419 : ℕ)^17*100000000000000^13 ≤ 81948464398013^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858784419 1000000000 81948464398013 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564692669/10000000000 : ℝ)^17 ≤ (4218325187429/25000000000000 : ℝ)^13 := by
    have hnat : (2564692669 : ℕ)^17*25000000000000^13 ≤ 4218325187429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564692669 10000000000 4218325187429 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617277/78125000 : ℝ)^17 ≤ (575309981/48828125000 : ℝ)^13 := by
    have hnat : (2617277 : ℕ)^17*48828125000^13 ≤ 575309981^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617277 78125000 575309981 48828125000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858784419/1000000000 : ℝ), (2564692669/10000000000 : ℝ), (-2617277/78125000 : ℝ)] ![(81948464398013/100000000000000 : ℝ), (4218325187429/25000000000000 : ℝ), (575309981/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858784419/1000000000 : ℝ)|^17 ≤ (81948464398013/100000000000000 : ℝ)^13
        have hw : |(858784419/1000000000 : ℝ)|=(858784419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564692669/10000000000 : ℝ)|^17 ≤ (4218325187429/25000000000000 : ℝ)^13
        have hw : |(2564692669/10000000000 : ℝ)|=(2564692669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2617277/78125000 : ℝ)|^17 ≤ (575309981/48828125000 : ℝ)^13
        have hw : |(-2617277/78125000 : ℝ)|=(2617277/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304052_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((22339/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22339/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91111/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91111/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-39787/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-39787/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18951/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18951/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78189/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78189/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30243/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30243/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (22339/25000 : ℝ) ^ (33/8 : ℝ) ≤ (62861587253879115099/100000000000000000000 : ℝ) := by
    have hpowers : (22339/25000 : ℝ)^33 ≤ (62861587253879115099/100000000000000000000 : ℝ)^8 := by
      have hnat : (22339 : ℕ)^33*100000000000000000000^8 ≤ 62861587253879115099^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22339 25000 62861587253879115099 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22339/25000 : ℝ)) (X := (62861587253879115099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (162861587253879115099/100000000000000000000 : ℝ) ≤ (11255116092169287/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (162861587253879115099/100000000000000000000 : ℝ)^8 ≤ (11255116092169287/10000000000000000 : ℝ)^33 := by
      have hnat : (162861587253879115099 : ℕ)^8*10000000000000000^33 ≤ 11255116092169287^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162861587253879115099 100000000000000000000 11255116092169287 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11255116092169287/10000000000000000 : ℝ)) (X := (162861587253879115099/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (112861587253879115099/50000000000000000000 : ℝ) ≤ (12181911221818321/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (112861587253879115099/50000000000000000000 : ℝ)^8 ≤ (12181911221818321/10000000000000000 : ℝ)^33 := by
      have hnat : (112861587253879115099 : ℕ)^8*10000000000000000^33 ≤ 12181911221818321^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112861587253879115099 50000000000000000000 12181911221818321 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12181911221818321/10000000000000000 : ℝ)) (X := (112861587253879115099/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1255116092169287/8935600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(463397564824517/4467800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (22339/25000 : ℝ)) (alpha := (1255116092169287/8935600000000000 : ℝ)) (beta := (463397564824517/4467800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22339/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1255116092169287/8935600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(463397564824517/4467800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (91111/100000 : ℝ) ^ (33/8 : ℝ) ≤ (68112936632541890323/100000000000000000000 : ℝ) := by
    have hpowers : (91111/100000 : ℝ)^33 ≤ (68112936632541890323/100000000000000000000 : ℝ)^8 := by
      have hnat : (91111 : ℕ)^33*100000000000000000000^8 ≤ 68112936632541890323^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91111 100000 68112936632541890323 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91111/100000 : ℝ)) (X := (68112936632541890323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (168112936632541890323/100000000000000000000 : ℝ) ≤ (5671020124807999/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (168112936632541890323/100000000000000000000 : ℝ)^8 ≤ (5671020124807999/5000000000000000 : ℝ)^33 := by
      have hnat : (168112936632541890323 : ℕ)^8*5000000000000000^33 ≤ 5671020124807999^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        168112936632541890323 100000000000000000000 5671020124807999 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5671020124807999/5000000000000000 : ℝ)) (X := (168112936632541890323/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (118112936632541890323/50000000000000000000 : ℝ) ≤ (12316962733870259/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (118112936632541890323/50000000000000000000 : ℝ)^8 ≤ (12316962733870259/10000000000000000 : ℝ)^33 := by
      have hnat : (118112936632541890323 : ℕ)^8*10000000000000000^33 ≤ 12316962733870259^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118112936632541890323 50000000000000000000 12316962733870259 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12316962733870259/10000000000000000 : ℝ)) (X := (118112936632541890323/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(671020124807999/4555550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(974922484254261/9111100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (91111/100000 : ℝ)) (alpha := (671020124807999/4555550000000000 : ℝ)) (beta := (974922484254261/9111100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (91111/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(671020124807999/4555550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(974922484254261/9111100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (39787/50000 : ℝ) ^ (33/8 : ℝ) ≤ (3896558107362923359/10000000000000000000 : ℝ) := by
    have hpowers : (39787/50000 : ℝ)^33 ≤ (3896558107362923359/10000000000000000000 : ℝ)^8 := by
      have hnat : (39787 : ℕ)^33*10000000000000000000^8 ≤ 3896558107362923359^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39787 50000 3896558107362923359 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39787/50000 : ℝ)) (X := (3896558107362923359/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13896558107362923359/10000000000000000000 : ℝ) ≤ (10830392132458759/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (13896558107362923359/10000000000000000000 : ℝ)^8 ≤ (10830392132458759/10000000000000000 : ℝ)^33 := by
      have hnat : (13896558107362923359 : ℕ)^8*10000000000000000^33 ≤ 10830392132458759^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13896558107362923359 10000000000000000000 10830392132458759 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10830392132458759/10000000000000000 : ℝ)) (X := (13896558107362923359/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (8896558107362923359/5000000000000000000 : ℝ) ≤ (11499187495012439/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (8896558107362923359/5000000000000000000 : ℝ)^8 ≤ (11499187495012439/10000000000000000 : ℝ)^33 := by
      have hnat : (8896558107362923359 : ℕ)^8*10000000000000000^33 ≤ 11499187495012439^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8896558107362923359 5000000000000000000 11499187495012439 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11499187495012439/10000000000000000 : ℝ)) (X := (8896558107362923359/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(830392132458759/7957400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8359942031921/99467500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (39787/50000 : ℝ)) (alpha := (830392132458759/7957400000000000 : ℝ)) (beta := (8359942031921/99467500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39787/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(830392132458759/7957400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8359942031921/99467500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-35471501/250000000 : ℝ)*X 0 0+(667451213/2000000000 : ℝ)*X 0 1+(-7480291307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1183869023/2500000000 : ℝ)*X 1 0+(-286641029/1000000000 : ℝ)*X 1 1+(-5231543339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5045411811/10000000000 : ℝ)*X 2 0+(3067209941/5000000000 : ℝ)*X 2 1+(606804339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1008021519/10000000000 : ℝ)*X 0 0+(1742614293/10000000000 : ℝ)*X 0 1+(-8819010437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1713721479/5000000000 : ℝ)*X 1 0+(-1960611923/10000000000 : ℝ)*X 1 1+(-3531787263/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1887535861/5000000000 : ℝ)*X 2 0+(1935518203/2500000000 : ℝ)*X 2 1+(41352047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1136279713/2500000000 : ℝ)*X 0 0+(3541160927/5000000000 : ℝ)*X 0 1+(-106274999/5000000000 : ℝ)*X 0 2+(1136279713/2500000000 : ℝ)*X 1 0+(3541160927/5000000000 : ℝ)*X 1 1+(-106274999/5000000000 : ℝ)*X 1 2+(1136279713/2500000000 : ℝ)*X 2 0+(3541160927/5000000000 : ℝ)*X 2 1+(-106274999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-210711707/10000000000 : ℝ)*X 0 0+(1913708317/10000000000 : ℝ)*X 0 1+(-905702381/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3021926113/10000000000 : ℝ)*X 1 0+(-558351721/2500000000 : ℝ)*X 1 1+(-1798509509/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7312018291/10000000000 : ℝ)*X 2 0+(105960833/250000000 : ℝ)*X 2 1+(306441813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4140805861/5000000000 : ℝ)*X 0 0+(3003715027/10000000000 : ℝ)*X 0 1+(-319084921/10000000000 : ℝ)*X 0 2+(4140805861/5000000000 : ℝ)*X 1 0+(3003715027/10000000000 : ℝ)*X 1 1+(-319084921/10000000000 : ℝ)*X 1 2+(4140805861/5000000000 : ℝ)*X 2 0+(3003715027/10000000000 : ℝ)*X 2 1+(-319084921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-19221/10000000000 : ℝ)*X 0 0+(4602348269/10000000000 : ℝ)*X 0 1+(-7087558221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6809627963/10000000000 : ℝ)*X 1 0+(-282735219/1250000000 : ℝ)*X 1 1+(-1741634669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((917808081/2500000000 : ℝ)*X 2 0+(7467829289/10000000000 : ℝ)*X 2 1+(975480763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((858784419/1000000000 : ℝ)*X 0 0+(2564692669/10000000000 : ℝ)*X 0 1+(-2617277/78125000 : ℝ)*X 0 2+(858784419/1000000000 : ℝ)*X 1 0+(2564692669/10000000000 : ℝ)*X 1 1+(-2617277/78125000 : ℝ)*X 1 2+(858784419/1000000000 : ℝ)*X 2 0+(2564692669/10000000000 : ℝ)*X 2 1+(-2617277/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18951/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18951/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (401872749712445707495776634389/64783696129618400000000000000000000 : ℝ) := by norm_num
    linear_combination (26164495211/62500000000 : ℝ)*(base7) + (15235397761/1000000000000 : ℝ)*(base39) + (71208997463/250000000000 : ℝ)*(base59) + (248708539291/100000000000 : ℝ)*(major_s1_0) + (248708539291/100000000000 : ℝ)*(major_s1_1) + (248708539291/100000000000 : ℝ)*(major_s1_2) + (8091543/1000000000000 : ℝ)*(sp_s1_0) + (2823139/1000000000000 : ℝ)*(sp_s1_1) + (614452031671/200000000000 : ℝ)*(sp_s1_7) + (614457152081/200000000000 : ℝ)*(sp_s1_8) + (1536148484767/500000000000 : ℝ)*(sp_s1_9) + (2058410783621/1000000000000 : ℝ)*(sp_s1_13) + (7179909/250000000000 : ℝ)*(sp_s1_14) + (838599/100000000000 : ℝ)*(sp_s1_15) + (409944715061/250000000000 : ℝ)*(f.failure) + (1536148484767/500000000000 : ℝ)*(f.sum) + (4031120570563118759/72500667140000000000000000000000 : ℝ)*base62 + (30109107288739/49733750000000000000000000 : ℝ)*base64 + (170556470541743/911110000000000000000000000 : ℝ)*base67 + (125838123384891/795740000000000000000000000 : ℝ)*base68 + (19943524951193141189/35552071720000000000000000000000 : ℝ)*base70 + (113911842361669/446780000000000000000000000 : ℝ)*base73 + (41339062186811/455555000000000000000000000 : ℝ)*base74 + (66744872897967/178712000000000000000000000 : ℝ)*base76 + (7671454087925361267/40706572580000000000000000000000 : ℝ)*base79 + (2251/3125000000000000 : ℝ)*base86 + (2251/3125000000000000 : ℝ)*base88 + (2251/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78189/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78189/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (399998632249015167850073067/35552071720000000000000000000000 : ℝ) := by norm_num
    linear_combination (512457348189/1000000000000 : ℝ)*(base7) + (23687063379/1000000000000 : ℝ)*(base39) + (412079/1000000000000 : ℝ)*(base49) + (2312239/1000000000000 : ℝ)*(base53) + (6982980987/62500000000 : ℝ)*(base59) + (2137538828011/1000000000000 : ℝ)*(major_s1_0) + (2137538828011/1000000000000 : ℝ)*(major_s1_1) + (534384128943/250000000000 : ℝ)*(major_s1_2) + (27592051/250000000000 : ℝ)*(sp_s1_8) + (1272460359803/500000000000 : ℝ)*(sp_s1_14) + (1272405175701/500000000000 : ℝ)*(sp_s1_15) + (636230757961/250000000000 : ℝ)*(sp_s1_16) + (960863220901/500000000000 : ℝ)*(sp_s1_20) + (1904329/40000000000 : ℝ)*(sp_s1_27) + (704658350919/500000000000 : ℝ)*(f.failure) + (636230757961/250000000000 : ℝ)*(f.sum) + (999186998184913617/18125166785000000000000000000000 : ℝ)*base62 + (12517123920039/79574000000000000000000000 : ℝ)*base64 + (3555115472348349/9111100000000000000000000000 : ℝ)*base67 + (435576844298883/1989350000000000000000000000 : ℝ)*base68 + (14899129009068778999/355520717200000000000000000000000 : ℝ)*base71 + (1188455570167727/4467800000000000000000000000 : ℝ)*base73 + (926076498929099/4555550000000000000000000000 : ℝ)*base75 + (1265264741386117/8935600000000000000000000000 : ℝ)*base77 + (186912198213461057681/407065725800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (4571/6250000000000000 : ℝ)*base87 + (4571/6250000000000000 : ℝ)*base89 + (4571/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30243/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30243/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (445213199301425111301602823/72500667140000000000000000000000 : ℝ) := by norm_num
    linear_combination (20262929289/62500000000 : ℝ)*(base7) + (10569/1000000000000 : ℝ)*(base15) + (389067830319/1000000000000 : ℝ)*(base39) + (40716652617/250000000000 : ℝ)*(base49) + (308090169679/1000000000000 : ℝ)*(base59) + (458788566403/200000000000 : ℝ)*(major_s1_0) + (458788566403/200000000000 : ℝ)*(major_s1_1) + (458788566403/200000000000 : ℝ)*(major_s1_2) + (13253527/1000000000000 : ℝ)*(sp_s1_2) + (5933629/62500000000 : ℝ)*(sp_s1_9) + (1436235414041/500000000000 : ℝ)*(sp_s1_21) + (2872470817513/1000000000000 : ℝ)*(sp_s1_22) + (2872362636491/1000000000000 : ℝ)*(sp_s1_23) + (1836643463391/1000000000000 : ℝ)*(sp_s1_27) + (1512436594767/1000000000000 : ℝ)*(f.failure) + (1436235414041/500000000000 : ℝ)*(f.sum) + (39818717738473713201/145001334280000000000000000000000 : ℝ)*base62 + (90428395037579/397870000000000000000000000 : ℝ)*base64 + (619302857893613/1822220000000000000000000000 : ℝ)*base67 + (244134849074971/318296000000000000000000000 : ℝ)*base68 + (317190847148547971/14220828688000000000000000000000 : ℝ)*base71 + (267652646145991/893560000000000000000000000 : ℝ)*base73 + (77065478889509/113888750000000000000000000 : ℝ)*base74 + (883097988960459/1787120000000000000000000000 : ℝ)*base76 + (5233356630513066413/81413145160000000000000000000000 : ℝ)*base78 + (53/12500000000000000 : ℝ)*base87 + (53/12500000000000000 : ℝ)*base89 + (53/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((22339/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22339/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91111/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91111/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-39787/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-39787/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18951/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18951/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78189/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78189/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-30243/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-30243/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304052_s1 p hpa hpb X hX hprev0

#print axioms solution
